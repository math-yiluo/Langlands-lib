# Free tensor factors preserve cohomological triviality

`Langlands.Tate.FreeTensorCohomologicalTriviality` states that, for a finite
group `G`, an integral representation `A` that is cohomologically trivial
remains so after tensoring with any integral representation `B` whose
underlying integral module is free. The tensor representation has the
diagonal `G` action. There is no condition on the rank or action of `B`.
All carriers lie in arbitrary common `Type u`, and the scalar ring is
`IntegralScalar`, the specified universe lift of the integers.

Both hypotheses and conclusion use
[`IsCohomologicallyTrivial`](CohomologicallyTrivial.md): the actual Tate
cohomology of every subgroup restriction must vanish in every integer
degree. Thus vanishing for the whole group alone is not the premise.

This is a restricted formulation of the corollary to Theorem 9 in Serre,
*Local Fields*, Greenberg translation, GTM 67 (1979), Chapter IX, Section 5,
printed p.145/PDF p.151. That corollary allows either tensor factor to be
torsion free, provided one is cohomologically trivial. Here `B` is required
to be free, which implies it is torsion free. The source tensor product is
over the integers; the Lean tensor product uses their specified universe
lift. These scalar rings are identified by `integralScalarEquiv`.

Serre's *Corrections to J-P. Serre's books* (2019), PDF pp.2–3, lists the
corrections for this edition of *Local Fields* and makes no change to this
corollary or to Chapter IX, Section 5.

The module defines the proposition only. It does not prove tensor
stability, identify scheme-valued torus cocycles with group cohomology, or
prove the Steinberg quasi-splitness theorem. The free-module restriction
is useful for a later application to integral torus lattices; the formal
comparison with those coefficients is a separate obligation.
