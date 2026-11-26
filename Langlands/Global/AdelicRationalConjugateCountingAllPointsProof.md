# Rational points in adelic conjugates of compact sets, at every adelic point: proof

Module `Langlands.Global.AdelicRationalConjugateCountingAllPointsProof` proves

`adelicRationalConjugateCountingAllPoints : AdelicRationalConjugateCountingAllPointsStatement.{u}`

(module `AdelicRationalConjugateCountingAllPointsStatement`; Mœglin–Waldspurger, *Spectral
decomposition and Eisenstein series*, I.2.4, Lemma (a)(i), printed pp. 25–26, with `y = x`). The
theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The source reduces the count to `GL_n` and calls the remaining estimate a simple exercise. The
proof below works directly with the matrix entries of `rho(γ)` and replaces the bound on
denominators by the product formula.

## Auxiliary results (namespace `RationalConjugateCountingAllPoints`)

- `Langlands.Analysis.card_le_of_separated_centres` gives the finite packing bound. In a finite-dimensional real normed space `E`, finitely many points of
  the closed ball of radius `R ≥ 0`, pairwise at distance at least `2ε > 0`, number at most
  `((R + ε) / ε)^(dim E)`. The balls of radius `ε` around them are disjoint and lie in the ball
  of radius `R + ε`; compare additive Haar measures. See [Discrete product subgroup counting](../Analysis/DiscreteProductSubgroupCounting.md).
- `finite_and_ncard_le_of_separated`: the same bound for an arbitrary set `P` whose images lie in
  the ball and are pairwise `2ε`-separated, together with the finiteness of `P` (an infinite `P`
  would contain finite subsets of every cardinality, `Set.Infinite.exists_subset_card_eq`).
- `le_pi_norm_infinite`: let `a ∈ F` be nonzero and `0 < t ≤ 1`. If the product over the finite
  places of the norms `‖a‖_v` of `a` in the completions is at most `t⁻¹`, then
  `t ≤ max_w ‖a‖_w`, the maximum over the archimedean places of the norms in the completions
  (the norm of the function `w ↦ a` in `∏_w F_w`). Proof: by the product formula in Mathlib,
  `∏_w ‖a‖_w^{mult w} = |N(a)|` (`InfiniteAdeleRing.coe_norm_eq_abs_norm`) and
  `∏_v ‖a‖_v = |N(a)|⁻¹` (`FiniteAdeleRing.coe_norm_eq_inv_abs_norm`,
  `FiniteAdeleRing.norm_eq_finprod_of_isUnit`), so `t ≤ |N(a)|`. If `s = max_w ‖a‖_w < t ≤ 1`,
  then `|N(a)| ≤ s^{∑_w mult w} ≤ s < t`, as there is an archimedean place and
  `mult w ≥ 1` (`InfinitePlace.mult_pos`).

## The theorem

Fix `F`, `G`, `rho : MatrixRepresentation G (Fin n)` with `n > 0` and `IsClosedSubgroup rho`.
Choose real normed-space structures on the archimedean completions
(`exists_normedSpace_real_infiniteCompletion`), let
`E = Fin n → Fin n → ∏_w F_w` with the sup norm and `m = dim_ℝ E`, and take `d = 6m`.

Given a compact `C`, the height `adelicHeight` (continuous, `continuous_adelicHeight`) is at most
`L = max 1 b` on `C`; take `B = 3^m L^{3m}`. Given `x`, let `H = ‖x‖ ≥ 1` and `R = L H² ≥ 1`. For
`γ` in `P = G(F) ∩ x C x⁻¹` write `M_γ = adelicMatrix γ ∈ GL_n(𝔸)` and let
`p(γ) ∈ E` be the family of archimedean components of the entries of `M_γ`.

1. *Height.* For `γ = x y x⁻¹`, submultiplicativity and inversion invariance of the height give
   `height(M_γ) ≤ H · L · H = R`.
2. *Rational matrices.* `M_γ = AdelicGL.rational F n Q_γ` for a rational matrix `Q_γ`, by the
   naturality of rational points (`AdelicGroupPoints.rational_naturality`,
   `GeneralLinearGroupPoints.adelicHomeomorph_rational`); so every entry of `M_γ` is the diagonal
   image of an element of `F` (`AdelicGL.rational_apply`).
3. *Archimedean bound.* `sublevel_subset` bounds every archimedean entry norm of `M_γ` by `R`,
   so `‖p(γ)‖ ≤ R`.
4. *Finite places.* Each entry of `M_γ` has norm at most `finiteLocal F n M_γ v` at the finite
   place `v` (`entry_le_localMaximum`), these local maxima are at least `1`, and their product
   is at most `height(M_γ) ≤ R`, because the archimedean factor of the height is at least `1`.
5. *Separation.* Let `γ ≠ γ'` in `P`. Injectivity of `adelicMatrix`
   (`isClosedEmbedding_adelicMatrix`) gives `Q_γ ≠ Q_γ'`, hence an entry `(i, j)` with
   `c = (Q_γ)_{ij} - (Q_γ')_{ij} ≠ 0`. At each finite place the ultrametric inequality gives
   `‖c‖_v ≤ max(‖(M_γ)_{ij}‖_v, ‖(M_γ')_{ij}‖_v) ≤ finiteLocal(M_γ, v) · finiteLocal(M_γ', v)`,
   so `∏_v ‖c‖_v ≤ R²` by step 4. By `le_pi_norm_infinite` with `t = R⁻²`, some archimedean norm
   of `c` is at least `R⁻²`; this norm is that of the `(i, j)` component of `p(γ) - p(γ')`, so
   `dist(p(γ), p(γ')) ≥ R⁻²`.
6. *Count.* With `ε = R⁻²/2`, `finite_and_ncard_le_of_separated` shows that `P` is finite and
   `#P ≤ ((R + ε)/ε)^m`. Since `(R + ε)/ε = 2R³ + 1 ≤ 3R³`, this is at most
   `(3R³)^m = 3^m L^{3m} H^{6m} = B ‖x‖^d`.

The exponent `d = 6m` depends only on `F` and `n`, and is chosen before `C`, as the statement
requires.
