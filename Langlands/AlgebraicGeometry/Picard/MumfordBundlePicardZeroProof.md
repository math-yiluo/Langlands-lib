# The actual Mumford family is geometrically Picard zero

Author: Worker 912.

`Langlands.AbelianScheme.mumfordBundlePicardZero` proves exactly the Library
proposition `Langlands.AbelianScheme.MumfordBundlePicardZeroStatement.{u}`,
for arbitrary universe `u`.

For every proof `preservation` of the canonical pullback-tensor comparison,
base scheme `S`, abelian scheme `A/S`, line bundle `L` rigidified along the
actual unit, ordinary line bundle `M` on `A`, and evaluation isomorphism
`L ⊗ M ≅ O_A`, the conclusion is

`IsPicardZeroFamily A (mumfordBundle A preservation L M evaluation)`.

Thus the actual constructed Mumford family on the parameter-first product
`A ×_S A` is invariant under every translation on every geometric fibre.
The canonical comparison proof remains universally quantified exactly as
in the target. There is no additional cube or triviality hypothesis.

## Implemented proof

The Lean proof applies the published reduction
`MumfordPicardZero.mumfordBundlePicardZero_of_cube` to the two published
theorems

- `Langlands.GroupScheme.fieldCubePullback`, imported from
  `Langlands.AbelianScheme.FieldCubePullbackProof`;
- `Langlands.AlgebraicGeometry.Picard.fieldLineBundleTriviality`, imported
  from `Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof`.

These discharge both premises of the reduction. This module adds only
that final composition; the geometric comparisons are implemented in
`MumfordBundlePicardZeroReduction`.

More explicitly, the reduction tests a geometric parameter
`s : Spec K → A` and uses the actual product symmetry and iterated base
change prescribed by `IsPicardZeroFamily`. Write `X` for the resulting
abelian scheme over `Spec K`, `π` for its structure map, `ι : X → A` for
its non-parameter coordinate, and `a` for the point of `X` induced by `s`.
Its `mumfordFibreIso` identifies the fibre bundle with

`π^*(s^*M) ⊗ (t_a^*(ι^*L) ⊗ ι^*M)`.

This is an isomorphism of actual module sheaves, constructed using
pullback composition, the supplied tensor comparison, tensor symmetry
and associativity. The coordinate identities identify the parameter
coordinate as constant, the other coordinate as `ι`, and addition on
the product as translation by `a` followed by `ι`.

The first factor is translation invariant because translations commute
with `π`; no choice of scalar-line trivialization is needed for this
factor. For the second, `isTranslationInvariant_square` specializes the
field cube theorem to the two constant maps with values `a` and an
arbitrary point `x`, and the identity map of `X`. The constant pullbacks
are trivialized using `fieldLineBundleTriviality`, giving the actual
theorem-of-the-square isomorphism. Tensor associativity and symmetry,
together with the pullback of the supplied evaluation, then show that
`t_a^*(ι^*L) ⊗ ι^*M` is invariant under translation by `x`. The reduction
combines these invariances by tensoring and transports them across
`mumfordFibreIso`.

The cube theorem applies to the fibre abelian scheme because its
commutativity, smoothness, properness and geometric connectedness are
part of the existing abelian-scheme structure. The reduction does not
use algebraic closedness beyond the target's quantification of geometric
fibres. The arbitrary-base conclusion is precisely that fibrewise
condition.

## Provenance and scope

This is an internal composition of published Library theorems. The
underlying geometric motivation and source provenance are recorded in
`MumfordBundlePicardZeroStatement.md` and
`MumfordBundlePicardZeroReduction.md`; the cube proof and field-line
triviality proof retain their own paired explanations. No new external
source assertion is introduced here.

The theorem has the exact imported proposition as its type and uses the
actual family, pullbacks, tensor products, evaluation and translations.
It adds no representability, dual-existence, projectivity or ampleness
assumption and makes no such conclusion. The target pair and its imports
are unchanged.
