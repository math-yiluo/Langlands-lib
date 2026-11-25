# Balls of the norm form of a quadratic extension of a nonarchimedean local field

The module `Langlands.ClassFieldTheory.Local.QuadraticNormBall` proves that the sets
`{z ∈ E | v(N_{E/F} z) ≤ v(s)}` are compact open subgroups of a quadratic extension `E` of a
nonarchimedean local field `F`, and gives the quadratic character of `E / F` with values in `ℂ`.

## Content

Let `F` be a nonarchimedean local field (Mathlib's `IsNonarchimedeanLocalField`) and
`E = F(δ)` a quadratic extension with conjugation `c` (`hE : IsQuadraticInvolution c δ`,
`Langlands/Group/Unitary/Basic.lean`).

- `normSign E t ∈ {1, -1} ⊆ ℂ`: `1` if `t ∈ Fˣ` is a norm from `E`, `-1` otherwise. It is
  multiplicative (`normSign_mul'` in characteristic `≠ 2`, `normSign_mul` its form for
  characteristic zero; from the index two of the norms, `mul_mem_range_norm_of_finrank_eq_two`)
  and equal to the Library's `normResidueSign F E`
  (`normSign_eq_normResidueSign`, under the instances `Algebra.IsQuadraticExtension F E`,
  `IsGalois F E`).
- `valuationBall s = {x | v x ≤ v s}` for `s ∈ Fˣ`: compact (`isCompact_valuationBall`) and open
  (`isOpen_valuationBall`).
- `valuation_two_mul_sq_le`: for a non-square `d`, `v(2a)² ≤ v(a² - d b²)`. Otherwise
  `1 - 4 (a² - d b²)/(2a)²` would be a square by Hensel's lemma for `X² + X + t`, making `d` a
  square.
- `exists_addSubgroup_norm_mem_valuationBall'` (characteristic `≠ 2`) and its form for
  characteristic zero `exists_addSubgroup_norm_mem_valuationBall`: the set
  `{z ∈ E | N z ∈ valuationBall s}` is a compact open additive subgroup of `E`. Writing `E = F ⊕ F δ` with `δ² = d` and
  `N(a + b δ) = a² - d b²`, the previous inequality makes the set of pairs `(a, b)` with
  `a² - d b²` in the ball closed under addition (`2(aa' - d bb')` is controlled by
  `(aa' - d bb')² - d(ab' - ba')² = (a² - d b²)(a'² - d b'²)`), and bounded (`v(2a)²`, `v(2db)²`
  are bounded by `v(s)` and `v(ds)`).

These are used by the Gauss integrals of the norm form (`Langlands/Theta/WeilIndex/NormForm.lean`)
and by the splitting scalar of the unitary dual pair (`Langlands/Theta/DualPair/LerayCharacter.lean`).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, under
`src/Development/AbelianVarietyTheory/`: `Definitions/Divisors/UnipVal.lean`, lines 50–51 (`sgn`);
under `Proofs/DivisorProofs/`: `LocalNormResidueSignMul.lean`,
`ExistsCompactOpenNormClosedBallQuadratic.lean` (each whole); from
`Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean` the closed balls `cball` with
`isOpen_cball`, `isCompact_cball` (lines 79–92). The repository has no licence file; the text is
used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `GlobalTheory.KSp` → `Langlands.LocalClassField`.
- Renamed: `sgn` → `normSign`, `sgn_mul_of_isQuad` → `normSign_mul` (proved from the Library's
  `mul_mem_range_norm_of_finrank_eq_two` (NYLL) instead of the source's class field theory),
  `cball` → `valuationBall`, `val_trace_sq_le` → `valuation_two_mul_sq_le`, `exists_normBall` →
  `exists_addSubgroup_norm_mem_valuationBall` (with the field and the extension implicit), the
  subgroup `ballSub` of pairs → the private `normFormBall`.
- New: `normSign_eq_normResidueSign`.

## Declarations

- `normSign`, `normSign_eq_normResidueSign`, `normSign_mul'`, `normSign_mul`.
- `valuationBall`, `isCompact_valuationBall`, `isOpen_valuationBall`.
- `valuation_two_mul_sq_le`, `exists_addSubgroup_norm_mem_valuationBall'`,
  `exists_addSubgroup_norm_mem_valuationBall`.

## Dependencies

`Langlands.ClassFieldTheory.Local.QuadraticNormIndex`, `Langlands.Group.Unitary.Basic`,
`Langlands.HarmonicAnalysis.Bicharacter.SelfDual` (`isOpen_setOf_valuation_le`); Mathlib:
`RingTheory.Henselian`, `Tactic.FieldSimp`.
