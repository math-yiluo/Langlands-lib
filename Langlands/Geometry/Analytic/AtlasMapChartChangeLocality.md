# Chart compatibility on actual inverse-image affinoid domains

Fix an original indexed affinoid atlas, two of its charts `i,j`, a presented
affinoid algebra `R`, and bounded algebra maps `φ : A_i → R` and `ψ : A_j → R`.
For every original common subchart `m` of `i,j`, form its full domain
`D = restrictionDomain m i` in chart `i` and the actual inverse-image full
domain `Q = Domain.pullback φ D` in the spectrum of `R`. Its algebra is the
previously constructed affinoid pushout quotient; `Q.baseMap` and
`Domain.pullbackMap φ D` are its two actual bounded structural maps.

The Prop-valued `IsLocalMapChartChange` requires the complete bounded equation
`Q.baseMap.comp ψ = (Domain.pullbackMap φ D).comp (restriction m j)` for every
such common original subchart. Thus the two induced local morphisms agree on
the actual inverse-image source domain. The definition has no arbitrary
coefficient-test quantifier and assumes neither a saturated atlas nor
comparable containing charts.

`isMapChartChange_iff_local` proves that this condition is equivalent to the
earlier `IsMapChartChange`, whose tests include all presented affinoid
algebras and all compatible bounded maps into them. The forward direction
tests that law on `Q.algebra` and its two structural maps. For the converse,
`Domain.pullback_test_factorization` first uses the full representation of
`Q` to factor any compatible test map `η` uniquely through `Q.baseMap`.
The representation of `D` then cancels its structural map and identifies the
second composite with the given test map `α`. Composing the local equation
with the resulting bounded map proves the arbitrary coefficient-test
equation. Equality of algebra maps is never deduced from spectrum equality
alone.

The constructed finite-cover chart change satisfies these local equations.
If the image of `φ` lies in chart `j`, they characterize that entire bounded
map uniquely. This is internal content derived from the previously
constructed pullback domains, their full representations, and bounded chart
change. No equivalence with an external definition of strong morphism, or
automatic compatibility of arbitrary original strong-map data, is asserted.
