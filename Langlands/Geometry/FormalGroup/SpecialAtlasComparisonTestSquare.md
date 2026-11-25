# Actual refined test comparisons around commuting coefficient squares

This module proves actual full-order test-comparison naturality around
a commuting square of supplied coefficient maps. The four coefficients maps
and the equality of their composites are given. Original, iterated and direct
finer chart choices may be independent, each with actual unit evidence.

The generic integral `Iso.square_paste` and `Iso.square_reverse` retain the
specified actual formal maps and prove their equations using full-order Hom
composition and the actual inverse laws. Integral atlas `Iso.onChart_trans`
and `Iso.onChart_symm` identify restriction of composition and inversion with
the same operations on the corresponding specified test charts.

`testIso_baseAlongEq` uses the actual identity atlas maps forced by equal
coefficient maps. Equality elimination reduces its equation to the proved
independence of finer test charts for the same actual extended comparison.

`testIso_baseAlongSquare` pastes the first route's coefficient-composition
square, the forced equality square and the reverse of the second route's
coefficient-composition square. The actual canonical square atlas map is
exactly that composite, and the proved chart restriction equations identify
its vertical maps. Thus the theorem identifies the complete integral formal
routes and their actual inverses. `baseAlongSquareTestSquare` rationalizes the
four same integral maps and packages their proved equation. No equality of
point evaluations or extra comparison compatibility premise is used.

All local-field, central-division and embedded-field hypotheses of actual
special atlases remain explicit. Coefficient rings have an independent universe.
The generic integral laws permit arbitrary finite coordinate types. Covers
may be infinite and scalar maps may merge generators. No original framed
comparison base change, comparison-class functoriality or representability
is asserted here.
