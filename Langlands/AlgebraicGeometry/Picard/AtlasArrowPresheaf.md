# The full arrow presheaf of an actual Picard family

This internal construction prepares the presentation used in the smooth
automorphism quotient argument. It imports the published actual relative
Picard pseudofunctor and its coherent point-fibre construction.

For an actual family `L` on `U`, `atlasArrowPresheaf f L` has, on every
`T : Over S`, a pair of actual morphisms `a, b : T → U` and an actual
isomorphism between their pullbacks of `L`. Its construction is the total
presheaf of the point fibre of `L` against itself, followed by the universe
lift used for algebraic-space presheaves. The two natural transformations
`atlasArrowFst` and `atlasArrowSnd` forget the isomorphism and retain the
respective maps. No restriction on a test scheme is imposed.

`classFamilyMap` is the Yoneda map of `L` into the unsheafified groupoid
isomorphism classes. `atlasArrow_classFamilyMap` proves that its composites
with the two projections agree, using the isomorphism retained by each
arrow. Conversely, `classFamilyMap_eq_iff` uses exactness of the quotient
by isomorphism to recover an actual arrow from equality of those
unsheafified classes.

The final two lemmas identify the composite with the existing etale
sheafification unit as the existing `etaleFamilyMap`, and prove equality
of the resulting two whole natural transformations into the etale class
sheaf. They do not assert that every sheaf section has a global line-bundle
representative, nor that equality after sheafification gives a global
arrow. Scheme representability of this presheaf, quotient construction,
and an etale atlas for the class sheaf remain separate obligations.

The provenance is internal: these are the full arrows and elementary
quotient comparisons of the already published relative Picard
pseudofunctor, assembled for the presentation in Artin's 1974 correction.
