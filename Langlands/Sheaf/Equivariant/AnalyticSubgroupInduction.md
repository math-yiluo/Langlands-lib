# Induction from an open subgroup preserves discreteness

This is an internal consequence of the published twisted analytic categories,
local action lifts, local-action discrete part, and subgroup induction. Let a
topological group `G` act on an analytic space `X`, let `H` be an open subgroup,
and let `Adm` be a translation-invariant condition on objects of the analytic
site. Coefficients are modules over a commutative ring `R`.

`mem_discreteSubmodule_of_subgroup_hom` proves that any morphism from a discrete
`H`-presheaf into the restriction of a `G`-presheaf has image in the latter's
`G`-discrete part. To test a local action after an arbitrary twisted restriction,
the proof factors that arrow through the translate by its twist. It translates
the tested action lift and restricts it to `H`. Discreteness over `H` supplies an
open subgroup fixing the translated image. Its image in `G` is open because
`H` is open. Conjugating back and intersecting with the tested acting subgroup
produces the required open fixing subgroup. Naturality and the conjugation
formula for local lifts identify its action on the original image.

`isDiscrete_subgroupLan` applies this image result to the left Kan extension
unit. The unit factors through the discrete part of the extension. The Kan
extension universal property extends this factorization to a retraction of the
discrete-part inclusion, so every section of the extension is discrete. This
step requires coproducts indexed by the right cosets of `H` and no refinement
hypothesis.

`isDiscrete_subgroupInduction` then uses the published discreteness theorem for
sheafification. It requires finite equivariant refinements on the twisted site
of `G`, together with sheafification; it requires no refinement hypothesis for
`H`. `discreteSheafSubgroupInduction` packages the resulting functor between
the full subcategories of discrete module sheaves. It is the published subgroup
induction functor on underlying sheaves.

This module supplies an induction construction needed for the open-subgroup
injective-preservation argument of
`Langlands.Sheaf.Equivariant.AnalyticSubgroupInjectives`. It does not assert an
adjunction on the discrete subcategories or prove the global cohomology
comparison.
