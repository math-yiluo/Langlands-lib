# Normal-base ample existence from two geometric inputs

Author: Worker 1318.

This internal reduction retains two explicit, unproved geometric inputs:

- `Langlands.AbelianScheme.NormalFiniteTypeTwoAxisExtensionProperty.{u}`,
  already defined in the Library's `NormalModelTwoAxisExtensionReduction`;
- `NoetherianAffineAbelianGenericAmpleStatement.{u}`, which asserts total
  ampleness of a given line bundle from its canonical generic ampleness.

The module does not prove either input or the unconditional existence target.
It preserves all normal finite-type integer domains and all actual abelian
schemes in `NormalFiniteTypeAbelianAmpleExistenceStatement.{u}`.

## Implemented construction

`normalFiniteTypeAbelian_exists_genericallyAmple_of_twoAxis` assumes the first
input and constructs an actual total line bundle with ample generic
restriction. For the canonical generic base change `B` of `A`,
`Langlands.GroupScheme.fieldAmpleExistence` supplies an ample line bundle.
`fieldAmpleDiagonalCorrespondence` then supplies an actual bundle `D` on
`B × B`, trivial on both unit axes, with ample diagonal restriction.
The assumed normal extension property gives an actual bundle `E` on
`A × A` and an actual module-sheaf isomorphism from its canonical generic
restriction to `D`.

The total bundle chosen by the proof is the pullback of `E` along the
actual diagonal of `A`. The canonical self-product restriction map
commutes with the diagonals: this is checked by its two pullback
projections. Pullback composition and that commuting square, followed by
the supplied restriction isomorphism for `E`, identify the generic
restriction of the chosen total bundle with the diagonal restriction of
`D`. `LineBundle.IsAmple.of_iso` transports its ampleness.

`normalFiniteTypeAbelianAmpleExistence_of_twoAxis_genericAmple` proves the
implication from the two displayed inputs to the entire published
`NormalFiniteTypeAbelianAmpleExistenceStatement.{u}`. A finite-type
integer algebra is noetherian by `Algebra.FiniteType.isNoetherianRing`.
Apply the preceding construction and then the second input to its chosen
total bundle. No polarization, chosen generic bundle, or dual scheme
occurs as a hypothesis of the existence statement being reduced.

## Provenance and dependency boundary

The proof is an internal composition of the published field ample-existence
proof, field ample diagonal correspondence, normal extension property
as an explicit argument, self-product comparison maps, and module-sheaf
pullback operations. Its diagonal argument specializes the implemented
argument of `valuationRingAmpleExtension_of_twoAxis` to the normal
finite-type extension input. The geometric motivation is the
correspondence-and-diagonal construction in Faltings–Chai, Chapter I,
Theorem 1.9, printed p.6; the generic ampleness criterion is described in
its own statement companion.

The module uses no scheme representability of the normal-base or
finite-type Picard sheaf, no smooth-family abelian representability
statement, and no proof of any such result. It constructs no dual scheme,
Picard atlas or Picard representer. It is conditional mathematics, not an
exact-target proof submission for Task 5655.
