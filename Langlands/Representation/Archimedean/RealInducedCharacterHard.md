# The induced–character filtration on `GL₃(ℝ)`: the case `t_c - a = -m'`

Module `Langlands.Representation.Archimedean.RealInducedCharacterHard` (namespace
`Langlands.Archimedean.RealInducedCharacter`).

## Role and provenance

This module is an internal step of the proof of `RealInducedCharacterFiltrationStatement`
(Task 7134; see `RealInducedCharacterFiltration.md`). It treats the one case the pushforward
of `RealInducedCharacterPushforward` does not cover. There, the stage-`2` piece would have
weight `ℓ - m' < ℓ`, so it is not admissible in `RealAdjacentFiltration`. In this case the
module builds a bijective exact intertwiner between the standard modules of `[c, d]` and
`[d, c]` directly.

The proof uses three main inputs:

* the two landing statements `RealSwapLandingCharacterFirstStatement` and
  `RealSwapLandingInducedFirstStatement` (Worker 763's module `RealSwapLandingStatement`).
  They are hypotheses here and are not proved in this module; `RealInducedCharacterFiltrationProof`
  supplies their proofs;
* the uncertainty principle `RealOrthogonalUncertainty.realOrthogonalBlockUncertainty`
  (Library);
* the `K`-count `RealKTypeTransport.surjective_of_injective_*` (Library).

No literature statement is formalized.

Notation. `d` has weight `m` and exponent `t`, and `ℓ = |m|`. `c` has parity `ε` and
exponent `s`. `a = aExp d = t + ℓ/2` and `b = bExp d = t - ℓ/2`. The hard case is
`s - a = -m'` with `0 < m'` and `2m' < ℓ`; then `s - b = ℓ - m' > 0`. `KF 3 ds` denotes the
`O(3)`-finite functions of `realStandardModule 3 ds`. `Φ^p_j` is the block Fourier
coefficient along `r_p`.

## General facts

* `modulo_of_coe_eq`: a linear map with the same values as an exact intertwiner (into a
  possibly different but equal-valued target submodule) is an exact intertwiner. It is
  proved from the two fields of `IsRealIntertwinerModulo` and the closure of standard modules
  under right translation and right derivatives.
* `coeff_eq_zero_of_blockFrobMap_eq_zero`: if a block Frobenius map kills `f`, then
  `Φ^p_j f = 0` on `O(n)` wherever `μ j ≠ 0`. This follows from
  `blockFourierCoefficient_blockFrobMap`.
* `eq_zero_of_blockFrobMap_eq_zero`: a block Frobenius map whose multiplier has no zeros on
  the parity class is injective. This is the previous lemma together with
  `blockFourierCoefficient_eq_zero_of_not_even` and `eq_of_blockFourierCoefficient_eq`.

## The lists

* `sl d = (ℓ + 1) mod 2`, the sign of the first position of the induction block `d`.
* `midList d c = [sgn^{ℓ+1}|·|^a, c, |·|^b]`, the list between the two standard modules.
* `realPositionCharacter_V`: `[sgn^{ℓ+1}|·|^a, |·|^b, c]` has the position characters of
  `[d, c]`.
* `realPositionCharacter_S`: `[c, sgn^{ℓ+1}|·|^a, |·|^b]` has the position characters of
  `[c, d]`. Both are checked position by position.
* `hsigma0_ca`, `hsigma0_ca'`, `hsigma0_cb`, `heven_pairParity_ca`, `heven_pairParity_ca'`,
  `heven_pairParity_cb`: the parity classes and symmetry signs of the pairs `(c, c_a)` and
  `(c_b, c)` reduce modulo `2` to `ε₀ = ℓ + 1 + ε` and to `ε`. These are the classes and signs
  of the landing statements.
* `data_S`: the Frobenius data along the block `0` from `[c, d]` to `midList d c`, for any
  multiplier symmetric for `pairParity c c_a`. The block `0, 1` contains the character `c`
  and the first position of `d`, so it straddles the induction block, and
  `IsBlockFrobData.of_mid` does not apply. The structure is therefore filled in directly:
  - the signs and exponents are checked position by position;
  - `induced_off` and `induced_p` are vacuous because `midList` has no induction block.
* `data_V`: the same along the block `1` from `[d, c]` to `midList d c`, for multipliers
  symmetric for `pairParity c_b c`.

## The hard case

* `highModes_of_tail_frob_eq_zero`: if a Frobenius map with multiplier `tailMultiplier ℓ' ε σ`
  (with `ℓ' - 1 ≡ ε`) kills `f`, then `Φ^p_j f = 0` on `O(n)` for `|j| ≥ ℓ'`. On the parity
  class, `|j| = ℓ'` is excluded by parity and the multiplier is nonzero for `|j| > ℓ'`.
* `hard_nu_b`: `s - b = ℓ - m'` as an integer.

### Case (i): `hard_iso_even`

Assume `hL' : RealSwapLandingCharacterFirstStatement` and that `ε - m' - ℓ` is even. Then
there is a surjective exact intertwiner `KF 3 [c, d] → KF 3 [d, c]`.

1. `A₀ = data_S` with the tail multiplier `tailMultiplier m'` for the class
   `pairParity c c_a`. The parity condition `m' - 1 ≡ pairParity c c_a` is the case
   hypothesis. The multiplier solves the recurrence for `δ = s - a + 1 = 1 - m'`
   (`isRecurrent_tailMultiplier`), so `A₀ : [c, d] → midList` is an exact intertwiner.
2. `A₁ = data_swap` of the last two characters, from `midList` to `[c_a, c_b, c]`. It uses the
   generic multiplier for `ν = s - b = ℓ - m'`, with `0 < Re ν`. By parity, `ν` is not of the
   form `pairParity c_b c + 2k + 1`, so the multiplier has no zeros.
3. Landing. Write `F = A₁ ∘ A₀`. For `f ∈ KF 3 [c, d]`, `hL'` applies to `f`, `A₀ f`, `F f`
   with `δ = 1 - m'`; then `δ + ℓ = s - b + 1`. The classes and signs are transported by the
   lemmas of the previous section. `hL'` gives `Φ⁰_k (F f) = 0` on `O(3)` for `|k| < ℓ`.
   Since `[c_a, c_b, c]` has the principal series of `[d, c]` (`realPositionCharacter_V`),
   `mem_realStandardModule_induced_character` puts `F f` in the standard module of `[d, c]`.
   So `F` restricts to `M : KF 3 [c, d] → KF 3 [d, c]`, an exact intertwiner by
   `modulo_of_coe_eq`.
4. Injectivity. Let `M f = 0`. Then `A₀ f = 0`, because `A₁` is injective
   (`eq_zero_of_blockFrobMap_eq_zero`). So `Φ⁰_j f = 0` on `O(3)` for `|j| ≥ m'`
   (`highModes_of_tail_frob_eq_zero`). As `f` lies in the standard module of `[c, d]`,
   `Φ¹_j f = 0` for `|j| < ℓ`. The uncertainty principle `realOrthogonalBlockUncertainty`
   (with `n = ℓ` along `r_1` and `n' = m' < ℓ` along `r_0`) gives `f = 0` on `O(3)`. A
   principal series function vanishing on `O(3)` is zero
   (`eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`).
5. Surjectivity follows from the `K`-count
   `RealKTypeTransport.surjective_of_injective_character_induced`.

### Case (ii): `hard_iso_odd`

Assume `hL : RealSwapLandingInducedFirstStatement` and that `ε - m' - ℓ` is odd. The
construction runs in the other direction.

1. `B₁ = data_V` with the tail multiplier `tailMultiplier (ℓ - m')` for the class
   `pairParity c_b c`. The parity condition `ℓ - m' - 1 ≡ ε` is the case hypothesis. The
   multiplier solves the recurrence for `δ = b - s + 1 = 1 - (ℓ - m')`, so
   `B₁ : [d, c] → midList` is an exact intertwiner.
2. `B₀ = data_swap` of the first two characters, from `midList` to `[c, c_a, c_b]`. It uses
   the generic multiplier for `ν = a - s = m' > 0`. By parity it has no zeros.
3. Landing. `hL` applies to `f ∈ KF 3 [d, c]`, `B₁ f`, `F f` (`F = B₀ ∘ B₁`) with
   `δ = 1 - (ℓ - m')`; then `δ + ℓ = a - s + 1`. It gives `Φ¹_k (F f) = 0` on `O(3)` for
   `|k| < ℓ`. Since `[c, c_a, c_b]` has the principal series of `[c, d]`
   (`realPositionCharacter_S`), `RealSwapFLanding.mem_realStandardModule_character_induced`
   (Worker 763) gives an exact intertwiner `M : KF 3 [d, c] → KF 3 [c, d]`.
4. Injectivity as in case (i). `B₁ f = 0` gives `Φ¹_j f = 0` for `|j| ≥ ℓ - m'`. The induction
   block of `[d, c]` gives `Φ⁰_j f = 0` for `|j| < ℓ`. Apply the uncertainty principle with
   `n = ℓ` along `r_0` and `n' = ℓ - m' < ℓ` along `r_1`.
5. Surjectivity follows from `RealKTypeTransport.surjective_of_injective_induced_character`.
   The inverse `M⁻¹` (`LinearEquiv.ofBijective`) is a surjective map `KF 3 [c, d] →
   KF 3 [d, c]`. It is an exact intertwiner by `modulo_of_comp_surjective`, since
   `M⁻¹ ∘ M = id` and `M` is a surjective exact intertwiner.

### `hard_filtration`

Assume both landing statements, `0 < m'`, `2m' < ℓ` and `s - a = -m'`. Then
`RealAdjacentFiltration 3 [] [] (induced d) (character c)` holds. The proof splits on the
parity of `ε - m' - ℓ` and takes the surjective exact intertwiner `L` of case (i) or (ii).
The filtration is the one-step filtration with the single piece `[c, d]` and the map `L`.
