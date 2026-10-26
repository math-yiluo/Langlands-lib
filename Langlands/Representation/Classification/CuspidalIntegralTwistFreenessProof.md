# Integral twist freeness of positive-rank cuspidal data

Author: Worker 495.

The theorem `Langlands.Classification.cuspidalIntegralTwistFreeness` proves
the exact published proposition
`Langlands.Classification.CuspidalIntegralTwistFreeness.{uF,uV} F T`.
Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
For every positive-rank actual cuspidal datum `ρ` and every integer `k`, it
proves `ρ.twist (k : ℝ) = ρ ↔ k = 0`.

This is an internal derivation of the published statement, using the
published admissible Schur theorem and residue-normalized uniformizer
calculation. There is no external theorem newly cited as a proof input.
The statement's central-character proof route is implemented here.

The helper `IntegralTwistFreeness.character_eq_one_on_center` compares an
irreducible admissible action with an equivalent scalar twist. The actual
central character is supplied by
`Langlands.admissibleSchur_centralCharacter`. Irreducibility supplies a
nonzero vector, and injectivity of the equivalence makes its image nonzero.
Intertwining and scalar central action give
`ω(z) • e(v) = (χ(z) * ω(z)) • e(v)`.
Cancellation on the nonzero vector and then cancellation of the nonzero
unit `ω(z)` force `χ(z) = 1` for every central element `z`.

The helper `IntegralTwistFreeness.scalar_uniformizer_value` evaluates
`T.determinantPowerCharacter r s` on the scalar matrix of
`LocalFactor.PadicAbelian.uniformizerUnit T`. It uses
`T.determinantNorm_scalar`, `coe_realPowerCharacter`, and
`T.normalizedAbs_uniformizer` to obtain `q^(-r*s)`, where
`q = T.residueCardinality`. The helper
`IntegralTwistFreeness.exponent_eq_zero_of_equiv` applies the central-action
result to this matrix. Since `T.residueCardinality_gt_one` gives `q > 1`,
`Real.rpow_right_inj` forces `-r*s = 0`; the positive-rank hypothesis then
gives `s = 0`. This helper works for real exponents, while the exact theorem
specializes it to integer exponents.

Equality of actual supercuspidal classes supplies an isomorphism of their
representatives in the full supercuspidal subcategory, using
`GeneralLinear.SupercuspidalRep.isoClass_eq_iff`. After quotient induction
on the base class, the proof forgets the inverse of that isomorphism and
uses `SmoothRep.equivOfIso` to obtain the correctly oriented equivalence
from the original action to its actual determinant twist. The real
exponent calculation and injectivity of the integer cast prove `k = 0`.
The reverse implication uses the published zero-twist identity through
simplification.

The field and representation-carrier universes remain independent.
Admissibility and irreducibility are extracted as `A.property.2.1` and
`A.property.1` from the supplied supercuspidal representative; they are
not added hypotheses of the exact theorem. In particular the proof does
not assert admissibility of arbitrary irreducible smooth representations.

The complete project import closure was checked recursively. The only
additional direct imports beyond the unchanged target are
`Smooth.Schur.Proof` and `LocalField.Uniformizer`. The former imports
`Smooth.Schur.Statement`, then `Smooth.Definitions`, and Mathlib. The latter
imports only `LocalField.Normalization.Definitions` and its lower local-field
definitions. The target's other imports concern the actual supercuspidal
category, twists and their admissibility, algebraic constituent relations,
block-factor induction definitions, smooth tensor constructions, Jacquet
coinvariant definitions, matrix groups, and local-field normalization.
No segment-constituent proof or higher classification module occurs in this
closure. The central-character and normalization results used here are actual
published theorems, rather than proposition definitions or pending proofs.

Consequently this proof is directly and transitively independent of individual
segment head/socle existence, segment analytic classification, special-head
product irreducibility, generic segment-product uniqueness, multisegment
exhaustion, ordered head or socle existence, quotient or socle coverage,
ordered conversion, tempered uniqueness, square-integrable classification
or exhaustion, and regular exhaustion. It supplies a focused freeness
prerequisite; it does not itself construct segment constituents.
