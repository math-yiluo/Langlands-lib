# High block modes after two block multipliers on `GL₃(ℝ)`: the mirror case

Module `Langlands.Representation.Archimedean.RealInducedCharacterLanding` (namespace
`Langlands.Archimedean.RealInducedCharacter`).

## Role and provenance

This module is an internal step of the proof of `RealInducedCharacterFiltrationStatement`
(Task 7134; see `RealInducedCharacterFiltration.md`). It is the mirror image of
`RealSwapFLanding.highModes_eq_zero` (Worker 763, Task 7133). The
roles of the two block rotations `r_0` and `r_1` are exchanged, and the test functions come
from the standard module of `[d, c]` instead of `[c, d]`. The proof follows the same duality
argument and uses the lemmas of `RealSwapFLanding`, `RealBlockTransposition` and the Library.
Its only nonstandard input is the landing statement `RealSwapLandingInducedFirstStatement`
(module `RealSwapLandingStatement`). The theorem takes that statement as a hypothesis and does
not prove it; it is proved as `RealSwapLandingIntegral.inducedFirst`. No literature statement is formalized.

Notation: `c : RealCharacterData` has parity `ε₁`; `d : ComplexCharacterData` has weight `m`;
`ℓ = |m|`; `ε₀ = ℓ + 1 + ε₁`. `Φ^p_j F = blockFourierCoefficient 3 p j F`, and `O(3)` is
`unitaryCompact ℝ 3`.

## Lemmas

* Imported `RealSwapLandingIntegral.realInducedBlockAt_induced_character`: the only induction block of `[d, c]` sits at
  position `0` and is `d`. The proof is a case analysis on the position.
* Imported `RealSwapLandingIntegral.mem_realStandardModule_induced_character`: let `f` lie in the principal series of the
  position characters of `[d, c]`, and let `Φ⁰_k f = 0` on `O(3)` for `|k| < ℓ`. Then `f`
  lies in `realStandardModule 3 [d, c]`. The proof uses `mem_realStandardModule_iff`. Modes
  of the wrong parity vanish everywhere by `blockFourierCoefficient_eq_zero_of_parity`. Modes
  of the right parity with `|k| < ℓ` lie in the window `window ℓ`. There the Library's
  propagation lemma `blockFourierCoefficient_window_eq_zero` extends vanishing on `O(3)` to
  all of `GL_3(ℝ)`; it needs the exponent equivariance of principal series functions
  (`isExpEquivariant_of_mem_principalSeries`). This lemma mirrors 763's
  `RealSwapFLanding.mem_realStandardModule_character_induced`.

## Main theorem

`highModes_eq_zero_mirror hL c d δ μ₀ μ₁ … e …`. Assume `hL :
RealSwapLandingInducedFirstStatement`. Let `μ₁` solve the recurrence for `δ` on the class
`ε₁` with symmetry sign `(-1)^{ε₁}`. Let `μ₀` solve the recurrence for `δ + ℓ` on the class
`ε₀` with sign `(-1)^{ε₀}`. Let `e ∈ ℕ`. Let `f, g₁, g, G` be continuous right `O(3)`-finite
functions on `GL_3(ℝ)`. Assume that on `O(3)`:

* `Φ¹_j f = 0` for `|j| ≥ ℓ`;
* `Φ⁰_j g₁ = μ₀ j · Φ⁰_j f` and `Φ¹_j g = μ₁ j · Φ¹_j g₁` for all `j`;
* `Φ⁰_j G = Φ⁰_j g` for `|j| ≥ ℓ` and `Φ⁰_j G = 0` for `|j| < ℓ`.

Assume further `G(diag(sgn a) κ) = χ(sgn a) · sgnDet(diag(sgn a))^e · G(κ)` for
`a ∈ (ℝˣ)³` and `κ ∈ O(3)`, where `χ` is the principal series character of
`realPositionCharacter [d, c]`. Then `Φ⁰_j g = 0` on `O(3)` for every `|j| ≥ ℓ`.

### Proof

1. Put `G' = G · sgnDet^e` and `φ = conj ∘ G'` on `O(3)`. `G'` is right `O(3)`-finite, so it
   is a polynomial in the matrix entries on `O(3)`
   (`OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors`). Hence `φ` is
   too, and its right translates span a finite-dimensional space
   (`TranslateFinite.finiteDimensional_span_eval`). By the sign hypothesis, `φ` transforms
   under the sign matrices by `χ`; this uses `sgnDet_pow_mul_self` and
   `conj_principalSeriesCharacter_signUnit`.
2. The Library's `principalSeriesExtension` gives a right `O(3)`-finite function `t` of the
   principal series of `[d, c]` with `t = conj G'` on `O(3)`. Its block-`0` modes `|j| < ℓ`
   vanish on `O(3)`. This follows from `hGlow`, from `blockFourierCoefficient_conj`, which
   sends `Φ⁰_j` to `Φ⁰_{-j}`, and from `blockFourierCoefficient_mul_sgnDet_pow`. By
   `mem_realStandardModule_induced_character`, `t` is an `O(3)`-finite function of the
   standard module of `[d, c]`.
3. Apply the reflected multipliers `j ↦ μ₁(-j)` along `r_1` and then `j ↦ μ₀(-j)` along `r_0`
   (`exists_multiplier`). This gives `t₀` and `u`. The reflected multipliers satisfy the same
   recurrences and symmetries (`isRecurrent_comp_neg`, `isSymmetric_comp_neg`). The landing
   statement `hL`, applied to `t, t₀, u`, gives `Φ¹_j u = 0` on `O(3)` for `|j| < ℓ`.
4. Twist the test functions by `sgnDet^e`. The transposition rule
   `integral_mul_eq_of_multiplier` (module `RealBlockTransposition`) and the orthogonality
   of complementary modes `integral_mul_eq_zero_of_modes` give
   `∫_{O(3)} G · conj G = ∫ g · t sgnDet^e = ∫ g₁ · t₀ sgnDet^e = ∫ f · u sgnDet^e = 0`.
   The first step uses the transposition with the indicator of the modes `|j| ≥ ℓ`: `G` and
   `g` have the same high modes, and the low modes of `G` and of `t · sgnDet^e` vanish. The
   last step holds because `f` has only block-`1` modes `|j| < ℓ` and `u` only block-`1`
   modes `|j| ≥ ℓ`.
5. So `G = 0` on `O(3)` (`eq_zero_of_integral_mul_conj`). Hence `Φ⁰_j g = Φ⁰_j G = 0` for
   `|j| ≥ ℓ`.
