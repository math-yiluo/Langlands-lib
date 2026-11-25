# Interlaced induction blocks: composites with intertwiners and mode expansions

Lean module: `Langlands.Representation.Archimedean.RealInterlacedJacquet`, namespace
`Langlands.Archimedean.RealInterlacedJacquet`.

This is the first of six modules that prove
`RealInterlacedInducedInducedLinkedJacquetFunctionalStatement` (module
`RealInterlacedLinkedJacquetStatement`). The modules are, in import order,
`RealInterlacedJacquet`, `RealInterlacedColumns`, `RealInterlacedChain`, `RealInterlacedEngine`,
`RealInterlacedProof` and `RealInterlacedMirror`. The final theorem is in `RealInterlacedMirror`;
its Markdown file explains the whole proof.

This module imports `RealBlockFlatJacquet` and through it the Library module
`RealCharacterCrossing`. It contains two independent toolkits: functionals
composed with intertwiners, and expansions of functions on matrices along block rotations.

## Notation

The notation is that of `RealBlockFlatJacquet.md`:

* `KF n ds` is the space of `O(n)`-finite functions of `realStandardModule n ds`, with the
  representation `π = realStandardRep n ds` of `O(n)` and `realStandardLie n ds`.
* `r_b(θ) = blockRotation n b θ`, `Φ^{(b)}_j(f)(g) = blockFourierCoefficient n b j f g`, and
  `coeff j F` is the `j`-th Fourier coefficient of a function `F` of `θ`.
* `ℓ_μ = blockJacquet n ds b μ` is the block Jacquet functional
  `ℓ_μ(f) = (2π)⁻¹ Σᶠ_j μ_j Φ^{(b)}_j(f)(1)` (Library).
* `PL τ e` is the list of characters `sgn^{e_i} |·|^{τ_i}`, and `frobMap hψ` is the Frobenius map
  of a real Jacquet functional `ψ` (module `RealCharacterCrossing`). `ia hb = b` and `ib hb = b + 1` are the two
  positions of the block `b`. `par hb e = (e_b + e_{b+1}) mod 2` is the parity class of the block.
* `RealLinkedJacquetFunctionalExists n ds` is the conclusion of the pair statements (module
  `RealLinkedJacquetPairReduction`, Library).

## Composites with intertwiners (section Composite)

Throughout, `B : KF n ds → KF n ds'` is a linear map that commutes with `O(n)` (`hrep`) and, where
needed, with the Lie algebra (`hlie`).

* `blockFourierCoefficient_rep`, `toUnits_mk`: `Φ_j(π(κ) w)(1) = Φ_j(w)(κ)` for `κ ∈ O(n)`.
* `blockFourierCoefficient_eq_zero_of_comp`: if `ℓ_μ ∘ B = 0` and `ℓ_μ` transforms under the sign
  matrices by signs `e`, then `Φ^{(r)}_j(B v)(κ) = 0` for every `κ ∈ O(n)` and every `j` with
  `μ_j ≠ 0`. Proof: the Frobenius function of `ℓ_μ` at `B v` vanishes on `O(n)`, and its `j`-th
  coefficient along `r_r` is `μ_j Φ_j(B v)(κ)`.
* `exists_of_comp_ne`: let `B` map into `KF n (PL τ e)`, with `τ_r - τ_{r+1} = k > 0` and
  `k + e_r + e_{r+1}` odd. If `ℓ_μ ∘ B ≠ 0` for the binomial multiplier
  `μ = binomialMultiplier k ε`, `ε = par`, then `RealLinkedJacquetFunctionalExists n ds` holds.
  This is the argument of `exists_of_comp` (`RealBlockFlatJacquet`) with the nonvanishing as a
  hypothesis: `isJacquet_cross` makes `ℓ_μ` a real Jacquet functional with `a_r - a_{r+1} = 1 - k`,
  and `blockJacquet_pow_eq_zero` gives the vanishing on `π(E_{r+1,r})^k`.
* `finsum_rightDerivative_flat_of`: the formula `finsum_rightDerivative_flat` of
  `RealBlockFlatJacquet` for one function `f`. Flatness is only required at the modes `j` with
  `Φ_j(f)(1) ≠ 0`.
* `isRealJacquetFunctional_comp_flat`: if `μ` is flat at the block `p` on the modes of all
  functions `B v` and symmetric for `σ`, then `ℓ_μ ∘ B` is a real Jacquet functional on `KF n ds`
  with the exponents `α` of `ds'` and with signs `e`. The signs satisfy `(-1)^{e_i} = χ_i(-1)` off
  the block and `(-1)^{e_i} = χ_i(-1) σ` on it. This is `isRealJacquetFunctional_blockJacquet_flat`
  with the hypotheses moved along `B`.
* `frobFun_comp_apply_of_mem`: on `O(n)` the Frobenius function of `ℓ_μ ∘ B` at `v` is
  `g ↦ (2π)⁻¹ Σᶠ_i μ_i Φ_i(B v)(g)`.
* `flat_sign_of`: `sgn` is flat for `δ = w + 1` on any coefficient sequence `c` with `c_j = 0` for
  `|j| < w` and off the class `j ≡ w + 1 (mod 2)`.
* `exists_of_dichotomy` (**the dichotomy**). Let `B` map into `KF n (PL τ e)`, and let
  `τ_b - τ_{b+1} = k₁ > 0` with `k₁ + e_b + e_{b+1}` odd. Let `e'` be `e` with both signs of the
  block `b` flipped. Let `τ_r - τ_{r+1} = k₂ > 0` with `k₂ + e'_r + e'_{r+1}` odd. Assume:
  whenever the window `|j| < k₁` of every `B v` vanishes at the block `b` on `O(n)`, some `v` makes
  the coefficient `coeff par' (θ ↦ Σᶠ_j sgn(j) Φ^{(b)}_j(B v)(r_r(θ)))` nonzero, where
  `par' = par hr e'`. Then `RealLinkedJacquetFunctionalExists n ds` holds. Proof: let `Λ` be the
  binomial functional for `k₁` at `b`. If `Λ ∘ B ≠ 0`, apply `exists_of_comp_ne`. Otherwise
  `blockFourierCoefficient_eq_zero_of_comp` gives the vanishing window, and parity
  (`blockFourierCoefficient_eq_zero_of_not_even`, Library) kills the other class. By
  `flat_sign_of`, `sgn` is then flat at `b` for `δ = k₁ + 1`. So `ψ = ℓ_sgn ∘ B` is a real
  Jacquet functional with the exponents of `PL τ e` and the signs `e'`
  (`isRealJacquetFunctional_comp_flat`, with `σ = -1`). Finally `exists_of_comp` applies to
  `frobMap hψ` at `r`. By `frobFun_comp_apply_of_mem` its nonvanishing hypothesis is the assumed
  nonzero coefficient.

The dichotomy needs no proof that `Λ ∘ B` vanishes or not: either alternative gives the
conclusion.

## Mode expansions (section Expansion)

`MF n` is the commutative ring of functions `Matrix (Fin n) (Fin n) ℝ → ℂ`.

* `IsExpansion b N H P`: `P` is a polynomial with coefficients in `MF n` of degree `≤ 2N`, and
  `H(r_b(t) X) = e^{-iNt} P(e^{it})(X)` for all `t` and `X`. The coefficient `P_k` is the mode
  `k - N` of `H` along `r_b`.
* `IsExpansion.apply`, `eval_map_eq_sum`, `expMode_one_pow`, `expMode_mul_expMode`: the expansion
  as the finite sum `Σ_{k ≤ 2N} P_k(X) e^{i(k - N)t}`.
* `isExpansion_zero`, `IsExpansion.add`, `IsExpansion.mul`, `IsExpansion.const_mul`: expansions
  add, multiply (orders add) and scale.
* `coeff_finset_sum_nat`, `coeff_sum_expMode`, `sum_ite_mode`, `sum_ite_mode_eq_zero`: Fourier
  coefficients of finite exponential sums.
* `blockFourierCoefficient_of_expansion`: if `f(r_b(t) κ) = H(r_b(t) κ)` for all `t`, then
  `Φ^{(b)}_j(f)(κ) = 2π P_{j+N}(κ)` for `0 ≤ j + N ≤ 2N`, and `0` otherwise (as a finite sum).
* `finsum_of_expansion`: `(2π)⁻¹ Σᶠ_j μ_j Φ^{(b)}_j(f)(κ) = Σ_{k ≤ 2N} μ_{k-N} P_k(κ)`.

### Submodules closed under expansion

* `HasExpTop b N S T`: every `H ∈ S` has an expansion of order `N` along `b` whose coefficients
  lie in `S` and whose top coefficient `P_{2N}` lies in `T`.
* `hasExpTop_mul`, `hasExpTop_one`, `hasExpTop_pow`: products of submodules (orders add, top
  coefficients multiply) and powers.
* `quad a₂ a₁ a₀` is the quadratic polynomial `a₂ X² + a₁ X + a₀`, with `coeff_quad`.
* `isExpansion_of_cos_sin`: if `g(r_b(t) X) = cos t A(X) + sin t B(X) + C(X)`, then `g` has the
  expansion of order `1` with `P = quad ((A - iB)/2) C ((A + iB)/2)`.
* `hasExpTop_span`: if every generator of `s` has an expansion of order `1` with coefficients in
  `span s` and top coefficient in `T`, then `HasExpTop b 1 (span s) T`.

The module compiles with no errors or warnings.

## Provenance

The method is internal to the proof of
`RealInterlacedInducedInducedLinkedJacquetFunctionalStatement`. It extends the flat-multiplier method of
`RealBlockFlatJacquet` from block Jacquet functionals on a standard module to their composites
with `(𝔤, K)`-intertwiners into principal series of characters, which are the Frobenius maps of
`RealCharacterCrossing`. It uses the Library's block Fourier coefficients, block
Jacquet functionals and multipliers (`RealBlockJacquetFunctional`, `RealBlockMultiplier`). The
expansions are elementary Fourier analysis on the circle.
