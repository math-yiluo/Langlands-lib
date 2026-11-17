# The group scheme on a stable normal model

Worker 336.

`Langlands.GroupScheme.DvrStableGroup.group G M` constructs an actual group
scheme on the source of a supplied `DvrStableNormalization.Model G.X`,
where `G` is a group scheme over a DVR `R`. Its underlying scheme over
`Spec R` is definitionally `M.source`. The morphism `map G M` is an actual
group-scheme homomorphism to `G` whose underlying morphism in `Over (Spec R)`
is definitionally `M.map`, as recorded by `map_hom`.

This is a construction conditional on the model data. It does not assert
the existence of the model or of a suitable DVR extension and does not
prove `DvrFiniteSmoothCoverStatement`.

## Construction of the operations

The helper `normalLift` chooses a lift of a specified morphism from a flat
scheme with normal stalks, using the surjectivity part of `M.normal_lift`.
The lemma `normalLift_fac` proves that composition with `M.map` recovers
the specified morphism. The model's uniqueness clause also makes this
chosen lift unique.

The unit of `G` lifts from `Spec R`, which is flat over itself and has
normal stalks because `R` is a valuation domain. The multiplication lifts
from the square of `M.source`; the inverse lifts from `M.source` itself.
The source and its square are normal by `M.normal_powers`. The lemma
`flat_power` proves flatness of every positive fibre power by induction,
using preservation of flatness under pullback and composition. The
lemmas `one_fac`, `mul_fac` and `inv_fac` give the three compatibility
equations with the ambient operations.

The definition `grpObj` applies
`Langlands.CategoryTheory.GroupObjectLift.grpObjOfInjective`. The
injectivity required on maps from the source and from its cube follows
from `M.normal_lift`, their flatness, and their normal stalks. Thus the
unit, associativity and inverse laws follow from the corresponding laws
on `G`. The definition `map` packages the compatibility equations for
unit and multiplication as a group homomorphism.

## Geometric properties

The theorem `smooth` assumes that `G` is locally of finite type over `R`
and proves that `group G M` is smooth. Finiteness of `M.map` implies local
finite type of the model over `R`; since a DVR is noetherian, this is also
local finite presentation. The structural map is flat by `M.flat`.
Each actual fibre is a group scheme, using the pullback group structure
`Over.grpObjMkPullbackSnd`, and is geometrically reduced by
`M.geometricallyReduced`. Mathlib's `AlgebraicGeometry.smooth_of_grpObj`
makes each fibre smooth over its actual residue field. The fibrewise
criterion `Smooth.of_smooth_fiberToSpecResidueField` then proves
smoothness of the structural map.

The theorems `quasiCompact` and `separated` inherit the corresponding
property from `G` by composition with the finite comparison map.
`affine_baseChange` says that, for every coefficient morphism
`b : T → Spec R`, affineness of the structural map of `b*G` implies
affineness of the structural map of `b*(group G M)`. The comparison map
remains finite after this pullback, and a finite morphism followed by an
affine morphism is affine. The lemmas `finite_map` and `surjective_map`
retain exactly the finite and surjective properties supplied by `M`.

## Provenance

This is an internal construction from the explicit
`DvrStableNormalization.Model` fields, the categorical construction in
`GroupObjectLift`, normality of valuation spectra from
`Picard.ValuationBaseNormality`, and the cited Mathlib group-smoothness
and fibrewise-smoothness theorems. It implements the group-operation
extension step without assuming that the finite model map is a
monomorphism. All rings, schemes and coefficient schemes remain in the
arbitrary universe `u`. The generic-isomorphism field of the model is
not needed by this construction.
