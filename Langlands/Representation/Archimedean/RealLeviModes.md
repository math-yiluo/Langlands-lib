# Torus modes and the annihilator of a real standard module

Lean module: `Langlands.Representation.Archimedean.RealLeviModes`.

This module is part of the proof of `RealStandardLanglandsQuotientStatement` (module
`RealLargeLanglandsQuotientReduction`). It
states and proves `Langlands.Archimedean.RealLeviModesStatement` (proof `realLeviModes`). The
statement describes the annihilator of the `O(N)`-finite part of a real standard module under the
`O(N)`-integral pairing with the principal series of the inverse characters, using the Fourier
modes along the rotations of the induction blocks.

This is internal infrastructure for the duality step of the single-shot Langlands-quotient
argument. No literature statement is claimed and nothing is cited; the provenance is internal
("derived"). Unprefixed lemma names below are in the namespace
`Langlands.Archimedean.RealLeviModes`.

## Notation

`GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ` and `O(N)` is the Library's `unitaryCompact ℝ N`, with
Haar probability measure `haarK N` (Library `RealPrincipalSeriesDuality`). From the Library:

* `blockFourierCoefficient N p j f g = ∫_0^{2π} f(r_p(θ) g) e^{−ijθ} dθ`, where
  `r_p(θ) = blockRotation N p θ` is the rotation in the coordinates `p, p + 1`. We write
  `Φ^p_j f` for it.
* `signReflection N i ∈ O(N)`: the diagonal matrix with `−1` at `i` and `1` elsewhere. We write
  `s_i`.
* `realStandardModule N ds`: the functions `f` in the principal series of the position
  characters `χ = realPositionCharacter ds` with `Φ^p_j f(g) = 0` for every `g`, every induction
  block `d` at a position `p` (`realInducedBlockAt ds p = some d`) and every `|j| < |d.weight|`.
* `kFiniteFunctions V (unitaryCompact ℝ N)`: the right `O(N)`-finite functions of `V`.
* `dualChar χ`: the pointwise inverse characters `χ⁻¹` (`PartialJacquet`), and `IsSignedPower`.

From earlier modules:

* `Slot N` and `coeffs` (module `RealInducedBlockBound`). A slot `s` records a position `s.p`
  with `s.p + 1 < N`, a weight `s.M` and a mode `s.j`. For a list `L = [s_0, …, s_{r−1}]`,
  `coeffs L F = Φ^{s_0.p}_{s_0.j} ⋯ Φ^{s_{r−1}.p}_{s_{r−1}.j} F`.
  `Slot.Disjoint s t` means the coordinate pairs `{s.p, s.p + 1}` and `{t.p, t.p + 1}` are not
  adjacent or overlapping. `IsKFin F` means `F` is right `O(N)`-finite.
* `setMode s j` (the slot `s` with mode `j`), `withModes S J` (the slots of `S` with the modes of
  the list `J`), `zeroModes S`, `HasDegree`, `coeffs_mul_right` and the Parseval formula
  `coeffs_zeroModes_mul_eq_sum` (module `RealInducedTorusCore`).
* `slots ds N`: the slots of the induction blocks of `ds`. The slot of a block `d` at the
  position `p` has weight `|d.weight|` (module `RealInducedStandardBound`, with `mkSlot`,
  `mem_slots`, `pairwise_slots`, `induced_at`, `isExpEquivariant_of_mem`, `exists_hasDegree`).

## The statement

`RealLeviModesStatement`: for every `N`, every list of real blocks `ds` with `realRank ds = N`,
with `χ = realPositionCharacter ds`, `X = realStandardModule N ds` and `S = slots ds N`:

1. for every `O(N)`-finite `v` in the principal series of `dualChar χ`:
   `∫_{O(N)} v(k) x(k) dk = 0` for all `O(N)`-finite `x ∈ X` **if and only if** `IsNull S v`;
2. for every `O(N)`-finite `x` in the principal series of `χ`:
   `∫_{O(N)} v(k) x(k) dk = 0` for all `O(N)`-finite `v` in the principal series of `dualChar χ`
   with `IsNull S v` **if and only if** `x` is an `O(N)`-finite element of `X`.

Here `IsNull S v` (definition `IsNull`) means: for every list of modes `J` with
`J.length = S.length` such that every slot `t ∈ withModes S J` has `t.M ≤ |t.j|`, the iterated
coefficient `coeffs (withModes S J) v` vanishes on `O(N)`. So all iterated coefficients of `v`
whose mode at every slot of weight `m` satisfies `|j| ≥ m` vanish on `O(N)`.

## Proof outline

The pairing `∫ v x` is expanded by Parseval along the slots. The window conditions of `X` (modes
`|j| < m`) and the null conditions of `v` (modes `|j| ≥ m` at every slot) are complementary. This
gives "null ⇒ annihilates". For the two converses, symmetrized coefficients are used. They are
equivariant under the sign reflections, and their conjugates extend from `O(N)` to the principal
series of the other character. A positivity identity then turns `∫ v x = 0` into vanishing of
coefficients.

## Results by section

**Signs** (section `Signs`).

* `blockRotation_mul_signReflection_of_mem` / `_of_not_mem`: `r_p(θ) s_i = s_i r_p(−θ)` if
  `i ∈ {p, p + 1}`, and `r_p(θ) s_i = s_i r_p(θ)` otherwise.
* `blockFourierCoefficient_signReflection_mul`: if `f(s_i g) = c f'(g)` for all `g`, then
  `Φ^p_j f(s_i g) = c Φ^p_{j'} f'(g)`, where `j' = −j` if `i ∈ {p, p + 1}` and `j' = j` otherwise.
* `symCoeffs L F`: the symmetrized iterated coefficient.
  `symCoeffs [] F = F` and
  `symCoeffs (s :: rest) F = Φ^{s.p}_{s.j}(symCoeffs rest F) + Φ^{s.p}_{−s.j}(symCoeffs rest F)`.
  `symCoeffs_signReflection_mul`: `F(s_i g) = c F'(g)` for all `g` implies
  `symCoeffs L F (s_i g) = c · symCoeffs L F' g`. It is continuous (`continuous_symCoeffs`) and
  right `O(N)`-finite (`isKFin_symCoeffs`) for continuous `O(N)`-finite `F`.
* `signReal_of_pos/neg`, `signUnit_of_pos/neg`: values of the sign functions.
* `apply_signDiagonal_mul`: if `χ_l(1) = 1` for all `l` and `φ : O(N) → ℂ` satisfies
  `φ(s_i κ) = χ_i(−1) φ(κ)` for all `i`, then
  `φ(signDiagonal a · κ) = principalSeriesCharacter ℝ N χ (sgn a) · φ(κ)` for every `a`. This is
  the hypothesis of the Library extension `extension_mem_kFiniteFunctions`. The proof is an
  induction over the number of leading coordinates whose sign is applied.

**Phase** (section `Phase`).

* `coeffs_blockRotation_mul`: for pairwise disjoint `L` and `t ∈ L`,
  `coeffs L F (r_{t.p}(φ) g) = e^{i t.j φ} coeffs L F g`.
* `blockFourierCoefficient_eq_zero_of_phase`: a function `c` with
  `c(r_p(θ) y) = e^{ijθ} c(y)` has `Φ^p_m c = 0` for `m ≠ j`.

**Torus averages** (section `Average`).

* `integral_blockRotation_mul`: `∫_{O(N)} G(r_p(θ) k) dk = ∫_{O(N)} G(k) dk` (left invariance).
* `exists_bound_of_continuous` and `integrable_of_continuous`: continuous functions are bounded and
  integrable on `O(N)`.
* `integral_blockFourierCoefficient_zero`: `∫_{O(N)} Φ^p_0 G = 2π ∫_{O(N)} G` for continuous `G`
  (Fubini and left invariance).
* `integral_coeffs_zeroModes`: `∫_{O(N)} coeffs (zeroModes L) G = (2π)^r ∫_{O(N)} G`, where
  `r = L.length`.

**Orthogonality** (section `Orthogonality`).

* `conj_exp_mul_I`: `conj(e^{ijθ}) = e^{−ijθ}`.
* `coeffs_zeroModes_mul_conj`: if `c` has the phase `e^{i t.j φ}` along every `t ∈ L`, then
  `coeffs (zeroModes L) (y ↦ F(y) conj(c(y))) g = conj(c(g)) · coeffs L F g`.
* `integral_mul_conj_coeffs`: for continuous `F` and pairwise disjoint `L`,
  `∫_{O(N)} F · conj(coeffs L F) = (2π)^{−r} ∫_{O(N)} |coeffs L F|²`.

**Variants** (section `Variants`).

* `variants L`: the `2^r` lists obtained from `L` by replacing each mode `s.j` by `±s.j`.
  `mem_variants_self`: `L ∈ variants L`.
* `forall₂_of_mem_variants`: a variant has the same positions and weights, with modes `±`.
* `exists_of_mem_of_forall₂`, `pairwise_of_forall₂`, `length_eq_of_forall₂`: list facts for
  `List.Forall₂`. Variants of a pairwise disjoint list are pairwise disjoint and have the same
  length.
* `continuous_list_sum`, `blockFourierCoefficient_list_sum`: `Φ^p_j` of a finite sum of continuous
  functions is the sum of the `Φ^p_j`.
* `symCoeffs_eq_sum`: `symCoeffs L F g = Σ_{L' ∈ variants L} coeffs L' F g` for continuous `F`.

**Vanishing** (section `Vanishing`).

* `exists_of_mem_right_of_forall₂`: list fact.
* `blockFourierCoefficient_symCoeffs_eq_zero`: for continuous `F`, pairwise disjoint `L`, `t ∈ L`
  and `j ∉ {t.j, −t.j}`, `Φ^{t.p}_j (symCoeffs L F) = 0` everywhere. Each variant has the phase
  `e^{±i t.j φ}` along `r_{t.p}`.
* `blockFourierCoefficient_of_eq_conj`: if `f = conj F` on `O(N)`, then
  `Φ^p_j f(k) = conj(Φ^p_{−j} F(k))` for `k ∈ O(N)`.
* `coeffs_eq_zero_of_mem`: for continuous `F`, pairwise disjoint `L` and `t ∈ L`, if
  `Φ^{t.p}_{t.j} F = 0` on `O(N)`, then `coeffs L F = 0` on `O(N)`. The block coefficients
  commute (`blockFourierCoefficient_coeffs`), and `O(N)` is stable under the rotations.
* `setMode_neg_mem_withModes`: `t ∈ withModes S J ⇒ setMode t (−t.j) ∈ withModes S (−J)`.
  `exists_setMode_mem_withModes`: if `J.length = S.length`, every `s ∈ S` occurs in
  `withModes S J` as `setMode s j` for some `j`.

**Positivity** (section `Positivity`).

* `eq_zero_of_integral_norm_sq_eq_zero`: a continuous `G` with `∫_{O(N)} |G|² = 0` vanishes on
  `O(N)`. The Haar measure has full support, through `Continuous.ae_eq_iff_eq`.
* `integral_mul_conj_sum`: for continuous `F` and a list `Ls` of pairwise disjoint lists of
  length `r`, `∫_{O(N)} F · conj(Σ_{L ∈ Ls} coeffs L F) = (2π)^{−r} Σ_{L ∈ Ls} ∫_{O(N)} |coeffs L F|²`.
* `coeffs_eq_zero_of_integral_symCoeffs`: for continuous `F` and pairwise disjoint `L`, if
  `∫_{O(N)} F · conj(symCoeffs L F) = 0`, then `coeffs L F = 0` on `O(N)`. The integral is
  `(2π)^{−r}` times a sum of non-negative terms, one of which is `∫|coeffs L F|²`.

**Extension** (section `Extension`). `exists_ext_conj`: let `χ` be signed-power characters
(`IsSignedPower χ e`) and `F` continuous and right `O(N)`-finite with
`F(s_i g) = conj(χ_i(−1)) F(g)` for all `i, g`. Then there is an `O(N)`-finite `f` in the
principal series of `χ` with `f(k) = conj(F(k))` for all `k ∈ O(N)`. Proof: `conj F` restricted
to `O(N)` is a polynomial in the matrix entries (Library
`OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors`), so its right translates
span a finite-dimensional space (`TranslateFinite.finiteDimensional_span_eval`). It transforms
under the sign matrices by `χ` (`apply_signDiagonal_mul`), and the Library
`extension_mem_kFiniteFunctions` and `extension_unitary` give `f`.

**Null functions** (section `Null`).

* `IsNull S v`: defined above.
* `integral_mul_eq_zero_of_isNull`: for pairwise disjoint `S`, continuous right `O(N)`-finite `v`
  with `IsNull S v`, and continuous `x` with `Φ^{s.p}_j x = 0` everywhere for all `s ∈ S`,
  `|j| < s.M`, we have `∫_{O(N)} v x = 0`. Proof: at `k ∈ O(N)`, Parseval
  (`coeffs_zeroModes_mul_eq_sum`, with `exists_hasDegree`) writes
  `coeffs (zeroModes S) (v x)(k)` as a finite sum of terms
  `coeffs (withModes S J) v (k) · coeffs (withModes S (−J)) x (k)`. If every slot of
  `withModes S J` has `M ≤ |j|`, the first factor is `0` by `IsNull`. Otherwise some slot has
  `|j| < M`, and the second factor is `0` by `coeffs_eq_zero_of_mem`. Then
  `integral_coeffs_zeroModes` gives `(2π)^r ∫ v x = 0`.

**The standard module** (section `Standard`).

* `even_of_neg_one_zpow_eq`: `(−1)^j = (−1)^{M+1}` in `ℂ` implies `Even (j + M + 1)`.
* `mem_kFin_standard_of_window`: if `realRank ds = N`, `x` is an `O(N)`-finite element of the
  principal series of `χ`, and `Φ^{s.p}_j x = 0` on `O(N)` for all `s ∈ slots ds N` and
  `|j| < s.M`, then `x` is an `O(N)`-finite element of `X`. For a block `d` at `p`: if
  `j + |d.weight| + 1` is even, `j` lies in the window of the Library's
  `RealBlockPropagation.blockFourierCoefficient_window_eq_zero`. Its exponent hypothesis
  `α_p − α_{p+1} = |d.weight| + 1` holds by `induced_at`, and that lemma propagates the vanishing
  from `O(N)` to `GL_N(ℝ)`. Otherwise the Library parity lemma
  `blockFourierCoefficient_eq_zero_of_parity` gives `Φ^p_j x = 0`, because
  `χ_p(−1) χ_{p+1}(−1) = (−1)^{|d.weight|+1}`.
* `blockFourierCoefficient_conj_symCoeffs_eq_zero`: if `f = conj(symCoeffs L F)` on `O(N)`
  (`F` continuous, `L` pairwise disjoint), `t ∈ L` and `|j| ≠ |t.j|`, then `Φ^{t.p}_j f = 0` on
  `O(N)`.
* `isNull_of_annihilates` (direction "⇒" of part 1): given `J`, let `L = withModes S J` and
  `P = symCoeffs L v`. Since `v(s_i g) = χ_i(−1)^{−1} v(g) = conj(χ_i(−1)) v(g)`
  (`|χ_i(−1)| = 1`), `exists_ext_conj` gives `f` in the `O(N)`-finite principal series of `χ`
  with `f = conj P` on `O(N)`. Then `f ∈ X` by `mem_kFin_standard_of_window`: at a slot `s` with
  `|j| < s.M ≤ |j'|`, where `setMode s j' ∈ L`, the previous lemma applies. So
  `0 = ∫ v f = ∫ v conj(P)`, and positivity gives `coeffs L v = 0` on `O(N)`.
* `mem_kFin_standard_of_annihilates` (direction "⇒" of part 2): for `s ∈ S` and `|m| < s.M`, let
  `L = [setMode s m]` and `P = symCoeffs L x`. By `exists_ext_conj` for `dualChar χ`, there is
  `v` in the `O(N)`-finite principal series of `dualChar χ` with `v = conj P` on `O(N)`. `v` is
  null. For allowed `J` the slot `setMode s j'` of `withModes S J` has `|j'| ≥ s.M > |m|`, so
  `Φ^{s.p}_{j'} v = 0` on `O(N)` by the previous lemma, and `coeffs_eq_zero_of_mem` applies. So
  `0 = ∫ v x = ∫ x conj(P)`, and positivity gives `Φ^{s.p}_m x = 0` on `O(N)`. Then
  `mem_kFin_standard_of_window` concludes.
* `window_of_mem_standard`: elements of `X` satisfy the window conditions at every slot,
  everywhere.
* `integral_mul_eq_zero_of_mem_standard` (both directions "⇐"): null `O(N)`-finite `v` pair to
  zero with `O(N)`-finite `x ∈ X`, by `integral_mul_eq_zero_of_isNull`.

`realLeviModes` assembles these four facts into `RealLeviModesStatement`.
