# Separating a point by smooth bumps pulled back along a map

Module `Langlands.Analysis.CompactFiberBumpSeparation`, namespace `Langlands.Analysis`.

## Statement

`CompactFiberBumpSeparationStatement` (universes `u`, `v`) asserts the following. Let

- `H : Type u` be a Hausdorff topological space with a measurable structure containing the
  open sets (`OpensMeasurableSpace H`, e.g. a Borel space);
- `μ` be a measure on `H` that is finite on compact sets (`IsFiniteMeasureOnCompacts μ`) and
  positive on nonempty open sets (`μ.IsOpenPosMeasure`);
- `M : Type v` be a finite-dimensional real normed space;
- `p : H → M` be continuous, `U ⊆ M` open and `h₀ ∈ H` with `p h₀ ∈ U`, such that
  `p ⁻¹' S` is compact for every compact `S ⊆ U`;
- `F : H → ℂ` be continuous and constant on the fiber of `p` through `h₀`: `p h = p h₀` implies
  `F h = F h₀`.

If `∫ h, (β (p h) : ℂ) * F h ∂μ = 0` for every `β : M → ℝ` that is smooth (`ContDiff ℝ ∞ β`),
has compact support (`HasCompactSupport β`) and satisfies `tsupport β ⊆ U`, then `F h₀ = 0`.

The theorem `eq_zero_of_integral_smoothBump_eq_zero` states the same assertion with its
hypotheses as arguments, and `compactFiberBumpSeparation` proves the statement from it.

## Provenance

The statement is internal. It was formulated, with this name and these hypotheses, as a lemma
for the Godement spanning argument of the equal-rank local Jacquet functional equation for
complex induced representations (Jacquet 2009, Theorem 2.1;
`ComplexLocalEqualFunctionalEquationStatement`), to be applied there to the square
complex Gram map. It is a standard measure-theoretic separation argument, and the statement
uses only Mathlib notions.

## Proof

The proof is by contradiction. Suppose `c := F h₀ ≠ 0`.

1. Put `G h := Re(c̄ · F h)`. `G` is continuous, `G h₀ = |c|² > 0`
   (`Complex.mul_conj`, `Complex.normSq_pos`), and `G` equals `G h₀` on the fiber of `p`
   through `h₀`.
2. Since `U` is open, there is `ε₀ > 0` with `ball (p h₀) ε₀ ⊆ U`. Put `r = ε₀ / 2`, so that
   `closedBall (p h₀) r ⊆ U`. Closed balls in `M` are compact (finite dimension), so
   `p ⁻¹' closedBall (p h₀) r` is compact. The set
   `A = p ⁻¹' closedBall (p h₀) r ∩ {G ≤ G h₀ / 2}` is a closed subset of it, hence compact.
3. `p h₀ ∉ p '' A`, because points of the fiber have `G = G h₀ > G h₀ / 2`. The image `p '' A`
   is compact, hence closed in `M`, so some ball `ball (p h₀) ε` misses it. Put
   `ε' = min ε r`.
4. Let `β` be Mathlib's smooth bump `ContDiffBump (p h₀)` with radii `ε'/2 < ε'`. Then
   `0 ≤ β ≤ 1`, `β (p h₀) = 1`, `support β = ball (p h₀) ε'` and
   `tsupport β = closedBall (p h₀) ε' ⊆ U`. Smoothness and compact support hold in finite
   dimension.
5. The real function `f h := β (p h) · G h` is continuous. Its support lies in the compact set
   `p ⁻¹' tsupport β`, so it has compact support (`HasCompactSupport.intro`, using `T2Space H`).
   It is nonnegative: if `β (p h) ≠ 0` then `p h ∈ ball (p h₀) ε'`. So
   `p h ∈ closedBall (p h₀) r` and `p h ∉ p '' A`, hence `h ∉ A` and `G h > G h₀ / 2 > 0`.
   Also `f h₀ = G h₀ ≠ 0`. By `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`,
   `∫ f dμ > 0`.
6. On the other hand, `f h = Re(c̄ · (β (p h) · F h))`, since `β` is real
   (`Complex.re_ofReal_mul`). The complex integrand is continuous with compact support, hence
   integrable. So `integral_re` and `integral_const_mul` give
   `∫ f dμ = Re(c̄ · ∫ β (p h) F h dμ) = Re(c̄ · 0) = 0` by the hypothesis applied to `β`. This
   contradicts step 5.
