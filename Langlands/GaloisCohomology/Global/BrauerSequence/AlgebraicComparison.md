# Algebraic Brauer classes and localization in the cochain model

`unitsRestrictionForEmbedding` gives the map on unit cohomology for a
field extension \(F/K\) and a \(K\)-embedding \(S\to T\) of the chosen
separable closures of \(K\) and \(F\). The map restricts along the
resulting homomorphism of Galois groups and applies the embedding to
the unit coefficients. All four fields share an arbitrary universe.

In degree two, the comparison with Mathlib's continuous cohomology
intertwines this map with continuous restriction. Naturality of the
algebraic Brauer comparison then identifies it with Brauer scalar
extension in `unitsRestrictionForEmbedding_brauerEquiv`.

For a number field, the restriction along each supplied place embedding
agrees with the cochain localization map. The proof compares the
decomposition homomorphisms by evaluating on the embedded closure and
compares the coefficient maps on units. Consequently
`brauerLocalization_brauerEquiv` and `realBrauerLocalization_brauerEquiv`
compute the finite and infinite localizations of an algebraic class by
extending the algebra to the actual completion. Applying the normalized
local invariant gives `localInvariant_brauerEquiv` at a finite place.
