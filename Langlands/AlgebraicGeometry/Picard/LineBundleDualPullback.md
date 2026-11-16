# Coherent pullback of actual dual line bundles

This internal derived module packages the existing canonical module duality
comparisons as isomorphisms of actual locally free rank-one sheaves, in every
scheme universe `u`.

`LineBundle.dualIso e` carries an isomorphism of line bundles to an isomorphism
of their existing internal dual line bundles in the same direction. Its forward
map is the internal dual of `e.inv`, and its inverse is the internal dual of
`e.hom`. Duality of module morphisms proves the inverse equations and the
identity, composition and symmetry laws.

For every base morphism `f : X → Y` and line bundle `L` on `Y`,
`LineBundle.isIso_dualPullbackComparison` proves that the existing canonical
module-sheaf comparison is invertible. Near each point, a line bundle is
isomorphic to the structure module. Invertibility for that module is preserved
under isomorphism, and the existing locality theorem globalizes it. There is
no affine or global trivialization hypothesis.

`LineBundle.dualPullbackIso f L` packages this exact comparison as an isomorphism
from the pullback of `L.dual` to the dual of the actual pullback of `L`. Its
naturality square for every line-bundle isomorphism uses the module comparison's
naturality applied to the inverse isomorphism. The identity and composition
lemmas follow from the established module dual-pullback coherence, after
cancelling the canonical module pullback isomorphisms. All equations use the
existing actual line-bundle identity and composition comparisons.

No new duality or determinant is introduced. These constructions use the
existing internal dual, rank-one condition and module dual-pullback map.
They assert neither ampleness nor representability of any moduli functor.
