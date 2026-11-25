# The splitting scalar

**GKT §12.4.2** in Case `3₊`: the Leray character `χ_V = χ` ((12.5), p. 376) on the Siegel Levi,
times the modulus `|det a|_E^{m/2}` of Proposition 12.27 (1) (p. 372), with the value
`β(m(a)) = χ(det a)` of Proposition 12.29 (p. 375) and the condition (11.2) (p. 317) on the Leray
splitting data `(χ, ψ)`.

The module `Langlands.Theta.DualPair.LerayCharacter` defines the scalar `χ(z) |N_{E/F} z|^{m/2}`
by which the Levi part of the Siegel parabolic acts in the Leray splitting of `U(ν, ν)`, and proves
its properties.

## Content

Let `F` be a nonarchimedean local field, `E` a field with `Algebra F E`, `χ : Eˣ →* Circle` and
`m ∈ ℕ`.

- `splittingScalar F χ m z = χ(z) |N_{E/F} z|_F^{m/2}` for `z ≠ 0` and `0` at `0`, with
  `|·|_F = distribHaarChar F` the modulus of `F`.

When `E / F` is a quadratic extension given by a quadratic involution and the restriction of `χ` to
`Fˣ` is the `m`-th power of the quadratic character of `E / F` (written as the source's condition
`ResEtaPow`), the internal lemma `sc_basic` gives: `splittingScalar 1 = 1`, multiplicativity, the
formula on units, `‖splittingScalar z‖² = |N z|^m`,
`splittingScalar (c z)⁻¹ · |N z|^m = splittingScalar z` (from `χ(c z) = χ(z)⁻¹`, `χ` being trivial on
norms), `splittingScalar t = (η(t) |t|)^m` for `t ∈ Fˣ` (`|N t| = |t|²`), and
`splittingScalar (z c(z)) = |N z|^m`. `sc_eventually_eq_one`: for continuous `χ`,
`splittingScalar z = 1` for `z` near `1`. The proof uses the subgroups
`{z ∈ E | v(N z) ≤ v(s)}`, which are compact and open
(`LocalClassField.exists_addSubgroup_norm_mem_valuationBall`). Near `1`, the powers of
`z` stay in a small neighbourhood on which `χ` is close to `1`, so `χ(z) = 1` (no small subgroups in
`ℂˣ`), and `v(N z) = 1`, so `|N z| = 1`.

Internal definition: `ResEtaPow` (the condition on `χ` written with the subgroup of norms). The
quadratic character with values in `ℂ` is `LocalClassField.normSign`. The public theorems of
`Langlands/Theta/DualPair/Unitary/Splitting.lean` state the condition on `χ` with the Library's
`LocalClassField.normResidueSign` and convert it.

Reference for the characters `χ`: Harris–Kudla–Sweet, *Theta dichotomy for unitary groups*, J. AMS
9 (1996), §1, (1.5), p. 951 (`χ_V|_{Fˣ} = ε_{E/F}^m` with `m = dim_E V` and `ε_{E/F}` the quadratic
character of `E/F`).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, under
`src/Development/AbelianVarietyTheory/`: `Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean`,
lines 396–408 (`ResEtaPow`, `ResEtaPow.map_conj`); `Definitions/Divisors/UnipVal.lean`, lines
120–123 (`sc`); under `Proofs/DivisorProofs/`: `UnitaryCharacterAbsScalarBasicProperties.lean`,
`UnitaryCharacterAbsScalarEventuallyEqOne.lean` (each whole). The source's `sgn` (`UnipVal.lean`,
lines 50–51), `LocalNormResidueSignMul.lean`, `ExistsCompactOpenNormClosedBallQuadratic.lean` and
the closed balls of `Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean` (lines 79–92) are
in `Langlands/ClassFieldTheory/Local/QuadraticNormBall.lean`. The repository has no licence file;
the text is
used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- `KSp.sc` → `Langlands.Theta.splittingScalar` (public); the rest in
  `Langlands.Theta.Unitary.Internal`.
- `nabs` → `distribHaarChar` (the casts between `ℝ≥0` and `ℝ` are written out); `nabs_pos`,
  `nabs_mul`, `nabs_one` → `distribHaarChar_pos`, `map_mul`, `map_one`.
- `ResEtaPow.map_conj` is proved from `IsQuadraticInvolution.map_map_eq_inv`.
- `SplitWeil.Model.secondCountable_and_t2_local_field`, `exists_cball_subset`,
  `eq_one_of_forall_pow_near`, `nabs_eq_one_of_valuation_eq_one` → Mathlib's instances and the
  Library's `exists_setOf_valuation_le_subset`, `complex_eq_one_of_forall_norm_pow_sub_one_lt`,
  `distribHaarChar_eq_one_of_valuation_eq_one`.

## Declarations

- `Langlands.Theta.splittingScalar`

## Dependencies

`Langlands.Theta.DualPair.Unitary.Form`, `Langlands.ClassFieldTheory.Local.QuadraticNormBall`;
Mathlib: `Analysis.SpecialFunctions.Pow.Real`, `RingTheory.Henselian`, `Tactic.FieldSimp`,
`Tactic.Positivity`.
