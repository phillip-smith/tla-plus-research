TLC      = tlc
TLATEX   = tlatex
SANY     = sany
PDFLATEX = pdflatex

WORKDIR = build
SRCNAME = WaterBottles
SRC  = $(SRCNAME).tla
CONF = $(SRCNAME).cfg
WORK = $(WORKDIR)/$(SRCNAME).tla
PDF  = $(WORKDIR)/$(SRCNAME).pdf
TEX  = $(WORKDIR)/$(SRCNAME).tex
AUX  = $(WORKDIR)/$(SRCNAME).aux
LOG  = $(WORKDIR)/$(SRCNAME).log

all: doc lint check

clean:
	rm -rf build $(SRCNAME).out states

$(WORK): $(SRC)
	mkdir -p $(WORKDIR)
	cp $< $@

$(TEX): $(WORK)
	@(cd $(WORKDIR) && $(TLATEX) -shade `basename $<`)

doc: $(TEX)
	@(cd $(WORKDIR) && $(PDFLATEX) `basename $<`)

lint: $(WORK)
	@(cd $(WORKDIR) && $(SANY) `basename $<`)

check: $(WORK) $(CFG)
	@(cd $(WORKDIR) && $(TLC) $< -config ../$(CONF))

dump: $(WORK) $(CFG)
	@(cd $(WORKDIR) && $(TLC) $< -config ../$(CONF) -dump state)
