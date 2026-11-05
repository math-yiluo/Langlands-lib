# Linearity of actual right-derived functors

This is an internal construction for an additive `R`-linear functor
`F : C ⥤ D`, where `R` is a ring, `C` and `D` are abelian `R`-linear
categories, and `C` has injective resolutions. The category and ring universes
are unrestricted by this file. No exactness or preservation-of-injectives
assumption on `F` is imposed.

The instance `Langlands.Cohomology.rightDerived_linear` proves that the
existing Mathlib functor `F.rightDerived n` is `R`-linear for every `n : ℕ`.
For a morphism `f : X ⟶ Y`, choose the actual chosen injective resolutions
`I` and `J` and the resolution lift `t` of `f`. The cochain map `r • t`
lifts `r • f`, because composition is bilinear and the lift commutes with
the augmentations in degree zero. The independently defined canonical
isomorphisms `I.isoRightDerivedObj F n` and `J.isoRightDerivedObj F n`
compute the two derived maps. Cancel the target comparison isomorphism,
then use linearity of the functor on complexes and of homology to identify
the scalar-multiplied maps. The homology-linearity instances are reused
from `Langlands.Cohomology.HyperextAbutment` in
`HyperextEdgeMapLinear`; they are not reproved or postulated here.

`rightDerivedHomLinearMap F n` packages the actual map of `F.rightDerived n`
on a hom space as an `R`-linear map. Its additivity proof uses the sum of
two resolution lifts in Mathlib's `rightDerived_map_eq` formula, followed
by additivity of the functor on complexes and homology and bilinearity of
composition. Its scalar law is the preceding instance.
`rightDerivedHomLinearMap_apply` records that its value is the existing
derived-functor map, by definition.

The provenance is internal: these are formal consequences of the actual
right-derived-functor construction, its resolution comparison formula,
and the published linear structure on homology. They introduce no
additional assumptions, axioms or geometric existence claims.
