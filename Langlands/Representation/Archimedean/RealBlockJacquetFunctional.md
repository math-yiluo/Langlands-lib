# Block Fourier multiplier functionals as real Jacquet functionals

Module `Langlands.Representation.Archimedean.RealBlockJacquetFunctional`, namespace
`Langlands.Archimedean.RealBlockJacquet`. It imports `RealBlockFourierFinite` (finiteness and
signs of block Fourier coefficients), `RealBlockLeftDerivative` (the tridiagonal formula),
`RealBlockMultiplier` (`IsRecurrent`, `IsSymmetric`), `RealJacquetFrobeniusProof` (the
Frobenius function `frobFun`) and `RealStandardModuleGKModule` (the `(𝔤, K)`-module of a real
standard module).

## Role and provenance

This is internal infrastructure. It makes no claim from the literature and has no sources. It
serves the proof of `Langlands.Archimedean.RealCharacterPairFiltrationStatement`.
In that proof, the maps between the standard modules of `pre ++ [x, y] ++ post` and of
lists with the block `[x, y]` changed are built by Frobenius reciprocity from linear
functionals. Those functionals weight the block Fourier coefficients at the identity by a
multiplier. This module proves that such a functional is a real Jacquet functional
(`IsRealJacquetFunctional`, Library `RealJacquetReduction`) when the multiplier satisfies the
recurrence and the symmetry of `RealBlockMultiplier`. It also computes the block Fourier
coefficients on `O(n)` of the resulting Frobenius function. It does not construct the
filtration and does not prove that the Frobenius function lies in a standard module.

## Notation

* `V = kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` are the `O(n)`-finite
  functions of the real standard module of the list of real blocks `ds`, with the Library
  `(𝔤, K)`-module structure `ρ = realStandardRep n ds` (right translation by `O(n)`) and
  `π = realStandardLie n ds` (right derivatives).
* `Φ_j f (g) = blockFourierCoefficient n p j f g = ∫₀^{2π} f(r_p(θ) g) e^{-ijθ} dθ` along the
  rotation `r_p(θ)` in the coordinates `p, q = p + 1`; `ia hp, ib hp : Fin n` are these two
  coordinates for `hp : p + 1 < n` (Library `RealBlockRotation`).
* `χ = realPositionCharacter ds`, the character at each diagonal position, and `χ_i(-1)`
  means `realPositionCharacter ds i (-1)`.
* Exponents: the hypothesis
  `hτ : ∀ (i : Fin n) (x : ℝ), χ i (e^x) = e^{τ_i x}` (with `e^x` as the unit
  `Units.mk0 (Real.exp x) _`) defines `τ : Fin n → ℂ`. Then `α_i = τ_i + (n - 1)/2 - i` is the
  `ρ`-shifted exponent, and `δ = α_p - α_q`. In the Lean statements `α_i` is written out as
  `τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)`.
* Parity: `ε : ℤ` with `hpar : (-1 : ℂ)^ε = χ_p(-1) χ_q(-1)`. By `RealBlockFourierFinite`,
  `Φ_j f = 0` for `f ∈ V` unless `j ≡ ε (mod 2)`.
* `IsRecurrent δ ε μ`: `μ(k + 2)(δ + k) = (k + 2 - δ) μ(k)` for `k ≡ ε`;
  `IsSymmetric ε σ μ`: `μ(-k) = σ μ(k)` for `k ≡ ε` (Library `RealBlockMultiplier`).

## Definitions

* `blockJacquet n ds p μ : V →ₗ[ℂ] ℂ`, the functional
  `ℓ_μ(f) = (2π)⁻¹ Σᶠ_j μ_j Φ_j f (1)` for a multiplier `μ : ℤ → ℂ`. It is defined for every
  `p`. The sum is finite because only finitely many `Φ_j f (1)` are nonzero
  (`exists_bound_coe`), and linearity uses this.

## Results

Elementary facts.

* `rotationGenerator_eq_zero`, `blockRotation_eq_one`: for `p + 1 ≥ N` the rotation generator
  is `0` and `r_p(θ) = 1`. `blockFourierCoefficient_of_not_lt`: then
  `Φ_k f (g) = 2π f(g)` for `k = 0` and `0` otherwise.
* `exists_bound`: for continuous right `O(N)`-finite `f` and every `p`, there is `D` with
  `Φ_j f (g) = 0` for `|j| > D` and `g ∈ O(N)`. For `p + 1 < N` this is
  `exists_blockFourierCoefficient_eq_zero` of `RealBlockFourierFinite`.
* `finite_support_of_bound`, `lt_abs_add`: finite support from a bound, and shifting a bound
  by at most `2`.
* `neg_one_pow_fin_add`: `(-1)^{(a + b).val} = (-1)^{a.val} (-1)^{b.val}` for `a b : Fin 2`.
* `RealStrictCharacterLanglandsQuotient.realPositionCharacter_one`, reused from
  `RealStrictCharacterLanglandsQuotient`: `χ i 1 = 1` for every position `i`.
* `blockFourierCoefficient_add` (continuous functions), `blockFourierCoefficient_smul`,
  `blockFourierCoefficient_zero_fun`: linearity of `Φ_j` in `f`.
* `continuous_blockFourierCoefficient`: `g ↦ Φ_k f (g)` is continuous for continuous `f`.
* `coeff_finset_sum` (continuous summands), `coeff_const_mul`, `coeff_finset_sum_expMode`:
  `coeff k (θ ↦ Σ_{i ∈ I} c_i e^{iiθ}) = c_k · 2π` if `k ∈ I`, and `0` otherwise.
* For `f ∈ V`: `continuous_coe`, `exists_bound_coe`, `finite_support_mul` (finite support of
  `j ↦ F j · Φ_j f (g)` for `g ∈ O(n)`), and `blockFourierCoefficient_eq_zero_of_not_even`
  (`hp`, `hpar`): `Φ_j f (g) = 0` for every `g` when `j - ε` is odd.
* `blockJacquet_apply`: the defining formula.

Right derivatives.

* `finsum_tridiagonal` (pure algebra): if `c : ℤ → ℂ` vanishes for `|j| > D` and off the
  parity class `ε`, and `IsRecurrent δ ε μ`, then for all `S, x, y, v : ℂ`
  `Σᶠ_j μ_j [(S - δ(x - y)/2 - i v j/2) c_j + ((x - y + iv)/4)(δ + j - 2) c_{j-2} +
  ((x - y - iv)/4)(δ - j - 2) c_{j+2}] = (S - (δ - 1)(x - y)) Σᶠ_j μ_j c_j`.
* `finsum_rightDerivative` (`hp`, `hτ`, `hpar`, `hrec : IsRecurrent δ ε μ`): for `f ∈ V`
  and an upper triangular real matrix `A`,
  `Σᶠ_j μ_j Φ_j(R_A f)(1) = (Σ_i α_i A_ii - (δ - 1)(A_pp - A_qq)) Σᶠ_j μ_j Φ_j f (1)`, where
  `R_A f = rightDerivative (matrixModel ℝ n) A f`.

Signs. These use only the symmetry of `μ`, not the recurrence.

* `blockJacquet_signReflection` (`hp`, `hpar`, `hsym : IsSymmetric ε σ μ` for any `σ : ℂ`):
  for `i : Fin n` and `f ∈ V`, `ℓ_μ(ρ(s_i) f) = χ_i(-1) σ ℓ_μ(f)` if `i = p` or `i = p + 1`,
  and `ℓ_μ(ρ(s_i) f) = χ_i(-1) ℓ_μ(f)` otherwise. Here `s_i = signReflection n i`.
* `blockJacquet_hsign`: under the same hypotheses, for signs `e : Fin n → Fin 2` with
  `(-1)^{e_i} = χ_i(-1)` for `i ≠ ia hp, ib hp`, `(-1)^{e_p} = χ_p(-1) σ` and
  `(-1)^{e_q} = χ_q(-1) σ`, one has `ℓ_μ(ρ(s_i) v) = (-1)^{e_i} ℓ_μ(v)` for all `i` and `v`.
  This is the hypothesis `hsign` of the Library `RealJacquetFrobenius.frobFun_eq`.

The Jacquet functional.

* `isRealJacquetFunctional_blockJacquet`: assume `hp`, `hτ`, `hpar`,
  `hrec : IsRecurrent δ ε μ` and `hsym : IsSymmetric ε σ μ`. Let `a : Fin n → ℂ` satisfy
  `a_i = α_i` for `i ≠ ia hp, ib hp`, `a_p = α_q + 1` and `a_q = α_p - 1`. Let `e` be signs as
  in `blockJacquet_hsign`. Then
  `IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) (blockJacquet n ds p μ) a e`.
  That is, `ℓ_μ` vanishes on `π(1 ⊗ X) V` for strictly upper triangular `X`, satisfies
  `ℓ_μ(π(1 ⊗ E_ii) v) = a_i ℓ_μ(v)`, and transforms under `s_i` by `(-1)^{e_i}`. Exponents
  and signs are those of `ds` except at the two block positions, where the exponents become
  `α_q + 1, α_p - 1` and the signs are multiplied by `σ`.

The Frobenius function. Let `a, e` be arbitrary and assume `hsign` (as produced by
`blockJacquet_hsign`). Write `B f = RealJacquetFrobenius.frobFun (realStandardRep n ds)
(blockJacquet n ds p μ) a e f`.

* `frobFun_apply_of_mem`: for `g ∈ O(n)`, `B f (g) = (2π)⁻¹ Σᶠ_i μ_i Φ_i f (g)`.
* `blockFourierCoefficient_frobFun` (`hp`): for `k ∈ O(n)` and all `j`,
  `Φ_j(B f)(k) = μ_j Φ_j f (k)`.
* `blockFourierCoefficient_frobFun_eq_zero`: let `p'` be a block disjoint from `p`
  (`p + 1 < p'` or `p' + 1 < p`). If `Φ^{p'}_i f (g) = 0` for every `g ∈ GL_n(ℝ)`, then
  `Φ^{p'}_i(B f)(k) = 0` for every `k ∈ O(n)`.

These describe `B f` on `O(n)` only.

## Proofs

* Degenerate rotations: for `p + 1 ≥ N` no entry of `rotationGenerator N p` has the required
  indices, so it is `0` and `r_p(θ) = exp(0) = 1`. Then `θ ↦ f(r_p(θ) g)` is the constant
  `f(g) · e^{i0θ}`, and `coeff_expMode` gives its coefficients.
* `realPositionCharacter_one`: by recursion on the list. For a character block it is
  `map_one`; for an induction block both characters are powers of `1`.
* `continuous_blockFourierCoefficient`: the integrand `(g, θ) ↦ f(r_p(θ) g) e^{-ikθ}` is
  jointly continuous (`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`).
* `coeff_finset_sum` distributes the interval integral over the finite sum
  (`intervalIntegral.integral_finsetSum`), each summand being continuous.
  `coeff_finset_sum_expMode` then applies orthogonality (`coeff_expMode`) and
  `Finset.sum_ite_eq'`.
* `blockFourierCoefficient_eq_zero_of_not_even`: if `j - ε` is odd then
  `(-1)^j = -(-1)^ε ≠ (-1)^ε`, and the parity lemma
  `blockFourierCoefficient_eq_zero_of_parity` of `RealBlockFourierFinite` applies, using
  `realPositionCharacter_one`.
* `blockJacquet` is linear because `Φ_j` is linear on continuous functions and the sums have
  finite support (`finsum_add_distrib`, `mul_finsum`).
* `finsum_tridiagonal`: split the sum into three sums with finite support. Shift the index of
  the second by `+2` and of the third by `-2` (`finsum_comp_equiv` with `Equiv.addRight 2` and
  `Equiv.subRight 2`), so that all three carry `c_j`. Recombine the three sums. For `j` off the
  parity class, `c_j = 0`. For `j` in it, the coefficient of `c_j` is
  `μ_j(S - δ(x - y)/2 - ivj/2) + ((x - y + iv)/4)(δ + j) μ_{j+2} + ((x - y - iv)/4)(δ - j) μ_{j-2}`.
  The recurrence at `j` gives `μ_{j+2}(δ + j) = (j + 2 - δ) μ_j`, and at `j - 2` it gives
  `μ_j(δ + j - 2) = (j - δ) μ_{j-2}`. Substituting, the coefficient becomes
  `μ_j(S - δ(x - y)/2 + (x - y)(1 - δ/2)) = (S - (δ - 1)(x - y)) μ_j`; the `v` terms cancel.
  The proof is `linear_combination` with these two identities.
* `finsum_rightDerivative`: `f` is smooth and, by `isExpEquivariant_of_mem_principalSeries`
  with `hτ`, satisfies `IsExpEquivariant α f`. The tridiagonal formula
  `blockFourierCoefficient_rightDerivative` of `RealBlockLeftDerivative` at `g = 1`, `X = A`
  writes `Φ_j(R_A f)(1)` in the form of `finsum_tridiagonal` with `c_j = Φ_j f (1)`,
  `S = Σ_i α_i A_ii`, `x = A_pp`, `y = A_qq` and `v = A_pq`.
* `blockJacquet_signReflection`: `ρ(s_i) f` is the right translate of `f` by `s_i`, so
  `Φ_k(ρ(s_i) f)(1) = Φ_k f (s_i)` (Library `blockFourierCoefficient_rightTranslation`). By
  `RealBlockFourierFinite` this is `χ_i(-1) Φ_{-k} f (1)` for `i ∈ {p, p + 1}` and
  `χ_i(-1) Φ_k f (1)` otherwise. In the first case the substitution `k ↦ -k`
  (`finsum_comp_equiv` with `Equiv.neg ℤ`) turns the multiplier into `μ_{-k}`, which equals
  `σ μ_k` on the parity class; off it `Φ_k f (1) = 0`. The constant is taken out with
  `mul_finsum`. `blockJacquet_hsign` compares the constants with `(-1)^{e_i}`.
* `isRealJacquetFunctional_blockJacquet`: `π(1 ⊗ X)` acts on `V` as the right derivative
  `R_X` (`realStandardLie_one_tmul_apply_coe`). A strictly upper triangular `X` is upper
  triangular with zero diagonal, so the factor of `finsum_rightDerivative` is `0`. For
  `X = E_ii` (`Matrix.single i i 1`) the factor is `α_i - (δ - 1)(x - y)` with `x = [i = p]` and
  `y = [i = q]`. This is `α_p - δ + 1 = α_q + 1` at `p`, `α_q + δ - 1 = α_p - 1` at `q` and
  `α_i` elsewhere, that is `a_i`. The sign clause is `blockJacquet_hsign`.
* `frobFun_apply_of_mem`: for `g ∈ O(n)`, `frobFun_eq` with the decomposition `g = 1 · g`
  gives `B f (g) = ℓ_μ(ρ(g) f)`, and `Φ_i(ρ(g) f)(1) = Φ_i f (g)`.
* `blockFourierCoefficient_frobFun`: for `k ∈ O(n)` and every `θ`, `r_p(θ) k ∈ O(n)`. So
  `B f (r_p(θ) k) = (2π)⁻¹ Σᶠ_i μ_i Φ_i f (r_p(θ) k) = (2π)⁻¹ Σ_{|i| ≤ D} μ_i Φ_i f (k) e^{iiθ}`,
  by the left rotation rule `blockFourierCoefficient_blockRotation_mul` and the uniform bound
  `D` on `O(n)`. Its `j`-th coefficient is `μ_j Φ_j f (k)` by `coeff_finset_sum_expMode`; for
  `|j| > D` both sides are `0`.
* `blockFourierCoefficient_frobFun_eq_zero`: as above,
  `B f (r_{p'}(φ) k) = Σ_{|j| ≤ D} (2π)⁻¹ μ_j Φ^p_j f (r_{p'}(φ) k)` with the uniform bound `D`
  for the block `p`. Each summand is continuous in `φ`, so the `i`-th coefficient along `p'`
  is `Σ_j (2π)⁻¹ μ_j Φ^{p'}_i(Φ^p_j f)(k)`. By `blockFourierCoefficient_comm` of
  `RealBlockFourierFinite` this is `Σ_j (2π)⁻¹ μ_j Φ^p_j(Φ^{p'}_i f)(k)`, and
  `Φ^{p'}_i f = 0`.
