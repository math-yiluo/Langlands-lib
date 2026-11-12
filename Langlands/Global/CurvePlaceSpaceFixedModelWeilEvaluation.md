# Original counit evaluation on curve-place space stages

This internal unit identifies the constructed fixed-model space Weil stage
homeomorphism with evaluation of the original counit, and proves the resulting
square with the literal full curve adele inclusions. It does not assert the
full adelic homeomorphism or independence of models.

Let `k` be finite, let `K` be a function field over `k`, and let `L/K` be finite.
Fix the principal S-integer presentation given by `s`, a finite-dimensional
extension of `k(s)` to `K`, and a nonzero chart element `t`. Write `S` for the
original `curvePlacePrincipalExceptional` support and let `T` contain `S`.
The upper initial and enlarged supports are their full upper preimages.
No separability assumption on `L/K` is made.

`levelInclusion` is the published `curvePlaceAdeleLevelInclusion` at `T`,
regarded over the original fixed lower and upper integral bases.
`levelInclusion_compatible` proves compatibility with these coefficient bases
using the literal completion inclusion on diagonal elements.
`upperStageFactorAlgHom` is the upper stage coordinate projection with the
fixed original coefficient action. It is obtained from the published factor
algebra equivalence by coordinate evaluation.
`levelInclusion_coordinate` identifies the projection after inclusion with
the original local coefficient map. The proof uses the published full-adele
projection formula, and applies integer subtype injectivity in the integral
case. `upperLevelFactorAlgHom` expresses the same upper projection into the
regrouped factor with its original coefficient algebra.

Let `X` be an actual algebraic space over the upper integral base. Assume that
`X` is separated and of finite type, its actual Weil sheaf is algebraic, and
the resulting Weil space is separated and of finite type. For the stage
comparison also retain a function-field structure on `L` and nonemptiness of
`S`, as in the original curve space stage construction.
`adelicLevelPointHomeomorph_eq_evaluation` identifies the stage homeomorphism
with `spaceWeilRestrictionEvaluation` along `levelInclusion`. The proof uses
injectivity of the upper stage coordinate homeomorphism and surjectivity of
the original place reindexing. Its local coordinate formula is replaced by
the general completed-tensor evaluation identity. Case analysis makes the
factor regrouping the identity, and upper coefficient naturality together
with `levelInclusion_coordinate` gives the required coordinate equality.
The upper support nonemptiness used here is the previously proved consequence
of lower support nonemptiness and surjectivity of place restriction.

`adelicEvaluation` is the original integral Weil counit along the literal full
curve adele inclusion. `adelicEvaluation_stage` proves that evaluation after
the lower stage inclusion equals the stage homeomorphism followed by the
upper stage inclusion. After the stage identity, lower and upper coefficient
naturality prove this square; the coefficient composition equations are the
literal inclusion identities.

The provenance is internal composition of the published original curve adele
inclusion, full-field coefficient formulas, actual fixed-level space Weil
homeomorphisms and their coordinate formulas, and general space counit
evaluation naturality. The hypotheses and original topologies are retained;
no full-adele bijectivity or continuity assertion is assumed in these proofs.
