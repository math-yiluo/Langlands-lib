# Actual common-Levi intertwining maps from regular germs

`comparisonFamilyOfRegularGerms` takes the two actual continued pairs,
ambient density of their genuine generic locus, and the existence of a
`RegularGermAt` at each unitary parameter. It produces an intertwining map
between the actual coefficient fibers at each of those parameters for the full
product of rational-point groups.

The proof first transports the actual generic intertwining map to the two
fixed compact carriers. The published compact comparison square identifies its
linear map with `compactComparison`. On the open set of any regular
representative, the numerator therefore intertwines the compact actions at
all generic parameters. For each fixed group element and input vector, the
difference of the two compositions is polynomial by the polynomial compact
action and the representative's polynomial numerator. Density and scalar
linear testing give its vanishing throughout the open set. Multiplying by
the inverse of the denominator at a regular point gives an intertwining map
on the compact carriers. Conjugation by the compact tensor equivalences gives
the actual map.

The compact value of the family is the chosen regular germ value. A
representative at one unitary point represents the germ at every unitary
point of its open domain. Uniqueness of that germ yields
`comparisonFamilyOfRegularGerms_isRegular`, using one whole-operator numerator
and denominator on that domain. The existing consequences of
`IsRegularUnitaryExtension` give agreement on the unitary generic locus and
uniqueness by the rational germ.

This is a derived step for the actual common-Levi tensor in Waldspurger's
Lemma V.3.1, printed p. 295 / PDF p. 61 (`waldspurger-2003-plancherel`). Its
inputs retain the two actual continued pairs and the ambient regularity
required in the published target.
