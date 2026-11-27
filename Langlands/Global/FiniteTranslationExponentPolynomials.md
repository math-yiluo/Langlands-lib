# Exponential polynomials in finite-dimensional translation-invariant function spaces

Module `Langlands.Global.FiniteTranslationExponentPolynomials` proves that every function in a
finite-dimensional space of functions, invariant under an action of `ℝ^ι` with continuous orbit
maps, is a finite sum of functions in the same space whose orbit maps are exponential polynomials.
It also supplies elementary facts on the polynomial function spaces `polynomialFunctions`
(module `Langlands.Global.AdelicLeadingCuspidalComponents`): the complex span of products of at
most `n` real-linear forms on a real vector space.

## Results

Polynomial functions on a real vector space `V`:

- `polynomialFunctions_mono`: `polynomialFunctions V m ≤ polynomialFunctions V n` for `m ≤ n`.
- `const_mem_polynomialFunctions`: constants lie in `polynomialFunctions V n`.
- `linear_mul_mem_polynomialFunctions`: if `f` lies in `polynomialFunctions V n` and `ℓ` is a
  real-linear form, `v ↦ ℓ(v) f(v)` lies in `polynomialFunctions V (n + 1)`.
- `comp_linearMap_mem_polynomialFunctions`: composition with a real-linear map `V' → V` maps
  `polynomialFunctions V n` into `polynomialFunctions V' n`.
- `linearForm_pow_sum_smul_mem_polynomialFunctions`: for continuous linear operators `Y i` on a
  complex normed space, a linear form `ℓ` and a vector `y`, the function
  `t ↦ ℓ((∑ i, t i • Y i)^k y)` on `ℝ^ι` lies in `polynomialFunctions (ι → ℝ) k`.

The decomposition, `exists_exponentPolynomial_decomposition`: let `ι` be finite,
`T : Multiplicative (ι → ℝ) →* Module.End ℂ (X → ℂ)` an action of `ℝ^ι` by linear operators on
the functions on a set `X`, and `W` a finite-dimensional subspace with `T t w ∈ W` for `w ∈ W`,
such that `t ↦ (T t w)(g)` is continuous for every `w ∈ W` and `g ∈ X`. Then there is `n` such
that every `w ∈ W` is a finite sum `w = ∑_{μ ∈ s} u μ` with `u μ ∈ W` and, for every `g`,

`t ↦ (T t (u μ))(g) · exp(-∑ i, t i μ i) ∈ polynomialFunctions (ι → ℝ) n`.

## Proofs

The polynomial facts are inductions over the span (`Submodule.span_induction`): a generator
`∏_{j < k} ℓ_j` multiplied by `ℓ` is the generator `∏_{j < k+1} (Fin.cons ℓ ℓ)_j`, and composed
with a linear map `L` it is the generator `∏ (ℓ_j ∘ L)`. For the iterates, induction on `k`:
`(∑ t i Y i)^{k+1} y = (∑ t i Y i)^k (∑ t i Y i y) = ∑ i, t i (∑ t j Y j)^k (Y i y)`, and each
summand is the coordinate `t i` times a polynomial of degree at most `k`.

For the decomposition, choose a basis of `W` (`Module.finBasis`) and transport the restrictions of
the operators `T t` to `E = Fin d → ℂ`, obtaining `A t : E →L[ℂ] E` with `A 0 = 1` and
`A (s + t) = A s * A t`. Continuity of `t ↦ A t` follows from continuity of `t ↦ A t y` for each
`y` (`continuous_clm_apply`); this in turn holds because `t ↦ T t w` is continuous into `W` with
the topology of pointwise convergence (`continuous_pi`), and the coordinate map of `W` is
continuous as a linear map on a finite-dimensional Hausdorff space
(`LinearMap.continuous_of_finiteDimensional`). By
`Langlands.Analysis.OneParameter.exists_exp_sum_of_continuous_add_mul`,
`A t = exp (∑ i, t i • X i)` with pairwise commuting `X i`. Over the algebraically closed field
`ℂ` the joint maximal generalized eigenspaces of the `X i` span `E`
(`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`), so
the coordinate vector of `w` is a finite sum of joint generalized eigenvectors `c μ`
(`Submodule.mem_iSup_iff_exists_finsupp`); `u μ` is the function with coordinates `c μ`. The value
`(T t (u μ))(g)` is `ℓ (A t (c μ))` for the linear form `ℓ` = evaluation at `g` composed with the
inverse coordinate map. By `Langlands.Analysis.OneParameter.exp_sum_smul_apply_of_mem`,
`ℓ (A t (c μ)) · exp(-∑ t i μ i) = ∑_{k < d} (k!)⁻¹ ℓ (N_t^k (c μ))` with
`N_t = ∑ i, t i (X i - μ i)`, a polynomial of degree at most `d = dim E` by the iterate lemma and
`polynomialFunctions_mono`.

## Provenance

This is the finite-dimensional form of the description of smooth `𝔷(A_M)`-finite functions on
`A_M` as linear combinations of the functions `a ↦ a^λ Q(log_M a)` in Mœglin–Waldspurger,
*Spectral Decomposition and Eisenstein Series* (1995), I.3.1, printed pp. 40–41, and of the
generalized eigenspace decomposition with polynomial components in Bernstein–Lapid, *On the
meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §6.2,
pp. 201–202, (6.3), here for a finite-dimensional space of functions instead of a space of smooth vectors.
