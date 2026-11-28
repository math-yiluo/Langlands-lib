# The extension and defined products

`sectionPair_mulG` identifies the extension evaluated at `(c,y)` with
the chart of `c` at `y`. The two maps agree on the dense open where
`cy` is defined, by the original chart formula.

`Triples.T3` is the scheme of triples with `(x,y)` and `(y,z)` in the
domain. The maps `Triples.L` and `Triples.R` send a triple to `(xy,z)`
and `(x,yz)`. They are generalizing by the open slice maps and flat
pullbacks used to form them. Hence the open on which both are in the
domain contains the generic points of `Triples.T3`. Associativity there
gives `mulG_assoc` by reducedness and separatedness, and evaluation on
scheme-valued points gives `mulG_assoc_pt`.

This is the dense associativity argument of BLR, *Néron Models*, §5.3
Lemmas 1–2, p. 120, applied to the extension on the square.
