# Decreasing averages of lattice coset tests near a graded nilpotent element

The module `Langlands.HarmonicAnalysis.UnitConjugation.IdempotentGradingAverage` proves the
geometric input of Howe's finiteness theorem for the Lie algebra of the unit group of an
algebra: near a nilpotent element `X₀` that is "lower triangular" for a grading of `A` by
orthogonal idempotents of a compact open order `R`, the indicator of a coset `x + L` of a large
element `x` (`L = ϖ ^ s R`) can be replaced, for every conjugation-invariant distribution, by an
`L`-invariant test supported on strictly smaller elements (`exists_decreasing_average`). All
declarations are in the namespace `Langlands.HarmonicAnalysis.UnitConjugation`. Lattices
`ϖ ^ k R` are `orderLevel R ϖ k` (module `OrderLevels`); coset indicators are
`latticeCosetTest` and `L`-invariant tests `latticeInvariantTests L` (module `LatticeTests`);
invariance of distributions is `IsConjugationInvariant` (module `InvariantDistribution`).

## Averaging over cosets

`A` is a topological ring, `L` an additive subgroup that is open and compact.

- `latticeCosetTest_apply_eq`: `latticeCosetTest L hLo hLc y z = if z - y ∈ L then 1 else 0`.
- `exists_conj_average`: let `M ≥ L` be a compact additive subgroup, `γ` a unit with
  `γ⁻¹ t γ ∈ M` for `t ∈ L`, and `x ∈ A`. Suppose every conjugation-invariant distribution `T`
  satisfies `T (1_{y + L}) = T (1_{x + L})` whenever `y - x ∈ M`. Then there is a Schwartz–Bruhat
  function `f ∈ latticeInvariantTests L`, with `γ⁻¹ z γ - x ∈ M` whenever `f z ≠ 0`, and
  `T f = T (1_{x + L})` for every invariant `T`. Proof: the image of `M` in `A ⧸ L` is finite
  (compact in a discrete space); with representatives `r q`, the indicator `g` of `x + M` is
  `∑_q 1_{x + r q + L}`, so `T g = N · T (1_{x + L})` with `N` the number of cosets. Take
  `f = N⁻¹ · (g ∘ Ad(γ⁻¹))`, that is `f(z) = N⁻¹ g(γ⁻¹ z γ)`: invariance of `T` gives
  `T f = N⁻¹ T g`, and `f` is `L`-invariant because `γ⁻¹ L γ ⊆ M`.

## Gradings by idempotents

For `e : ℕ → A`, `m : ℕ` and `c : ℕ → F`, `idemSum e m c = ∑_{i < m} c i • e i`. For orthogonal
idempotents (`e i * e i = e i`, `e i * e j = 0` for `i ≠ j`):

- `idemSum_mul_idemSum`: `idemSum e m c * idemSum e m d = idemSum e m (c · d)`;
- `idemSum_mul_mul_idemSum`: `idemSum e m c * Y * idemSum e m d =
  ∑_{i, j < m} (c i * d j) • (e i * Y * e j)` (no hypothesis needed);
- `mul_doubleSum_mul`: for `a, b < m`, `e a (∑_{i, j < m} f i j • e i Y e j) e b =
  f a b • e a Y e b`;
- with `∑_{i < m} e i = 1`: `eq_zero_of_ge` (`e a = 0` for `a ≥ m`), `eq_doubleSum`
  (`Y = ∑_{i, j < m} e i Y e j`), and `isLower_of_lt` (the condition `e i Y e j = 0` for `i ≤ j`
  holds for all `i, j` once it holds for `i, j < m`).

The grading element is `γ = idemSum e m (i ↦ ϖ ^ i)` with inverse `idemSum e m (i ↦ ϖ ^ (-i))`;
conjugation by `γ` multiplies `e i Y e j` by `ϖ ^ (i - j)`.

## Linear algebra and levels

- `exists_linear_rightInverse_commutator`: if every `w` in a subspace `N` is of the form
  `x y - y x`, there is a linear `σ : A →ₗ[F] A` with `x σ(w) - σ(w) x = w` for `w ∈ N`
  (a right inverse of the corestricted commutator map, composed with a projection onto its
  range).
- `exists_orderLevel_bound`: a linear map `σ` of the finite-dimensional `A` satisfies
  `σ(ϖ ^ k R) ⊆ ϖ ^ (k - b) R` for some `b : ℕ` and all `k` (continuity of `σ` for the module
  topology and `exists_orderLevel_subset`).
- `doubleSum_mem_orderLevel`: for `Y ∈ ϖ ^ k R` and `e i ∈ R`, the sum
  `∑_{i, j < m} ϖ ^ (f i j) • e i Y e j` lies in `ϖ ^ k' R` if for each `i, j < m` either
  `e i Y e j = 0` or `k' ≤ k + f i j`.
- `latticeCosetTest_eq_pullback_conj`: if a unit `g` and its inverse conjugate `L` into itself
  and `g x g⁻¹ - y ∈ L`, then `1_{y + L} = 1_{x + L} ∘ Ad(g⁻¹)`.

## The Newton step

`exists_unit_conj_sub_mem` (`R` a compact open order, `ϖ ≠ 0`, `valuation F ϖ < 1`, `A`
finite-dimensional): let `c ≤ s`, `X y - y X = w` with `w ∈ ϖ ^ c R` and `y ∈ ϖ ^ (c - b) R`,
`λ ∈ ϖ ^ (s - c + b) R`, and `h : ℕ` with `1 ≤ h + c - b` and `s ≤ h + 2c - b`. Then there is a
unit `g` with `g, g⁻¹ ∈ R` and `g x g⁻¹ - x - w ∈ ϖ ^ s R` for `x = ϖ ^ (-h) (X + λ)`. Proof:
`u = -ϖ ^ h y ∈ ϖ R`, so `g = 1 + u` has an inverse `v ∈ R` (`exists_inverse_one_add`). With
`E = u x - x u = w + δ`, `δ = λ y - y λ ∈ ϖ ^ s R`, one has
`g x v - x - w = δ + E (v - 1)` and `v - 1 = -u v`, so the error is in `ϖ ^ s R`. A single step
suffices because only the coset modulo `ϖ ^ s R` matters; no iteration or limit is needed.

## The decreasing averages

`exists_decreasing_average`: let `R` be a compact open order (`IsCompactOpenOrder F R`) of a
finite-dimensional algebra `A` over a nonarchimedean local field `F` with its module topology,
`ϖ ≠ 0` with `valuation F ϖ < 1`, and `e 0, …, e (m - 1)` orthogonal idempotents in `R` with
sum `1`. Let `X₀ ∈ R` satisfy `e i X₀ e j = 0` for `i ≤ j`, and assume every `w` with
`e i w e j = 0` for `i ≤ j` is a commutator `X₀ y - y X₀`. Then for every `s : ℤ` there are
`a, t : ℕ` such that for all `h ≥ t` and `λ ∈ ϖ ^ a R` there is
`f ∈ latticeInvariantTests (ϖ ^ s R)` with support in `ϖ ^ (1 - h) R` and
`T f = T (1_{x + ϖ ^ s R})`, `x = ϖ ^ (-h) (X₀ + λ)`, for every conjugation-invariant `T`.

Proof, with `L = ϖ ^ s R`, `a = m + b` and `t = 2m + b + |s| + 1`, where `σ` is the right inverse
of `y ↦ X₀ y - y X₀` on the lower-triangular subspace and `b` its level bound:

1. `M = L + γ⁻¹ L γ` is compact and contains `γ⁻¹ L γ`.
2. For `y - x = ℓ₁ + γ⁻¹ ℓ₂ γ` (`ℓ₁, ℓ₂ ∈ L`), split `γ⁻¹ ℓ₂ γ = w + q` into the strictly lower
   part `w = ∑_{j < i} ϖ ^ (j - i) e i ℓ₂ e j ∈ ϖ ^ (s - m) R` and the rest `q ∈ L` (exponents
   `j - i ≥ 0`). So `y + L = x + w + L`. The Newton step with `c = s - m` and `σ(w)` gives a
   unit `g ∈ R^×` with `g x g⁻¹ ≡ x + w (mod L)`, hence `1_{y + L} = 1_{x + L} ∘ Ad(g⁻¹)` and
   `T (1_{y + L}) = T (1_{x + L})` for invariant `T`.
3. `exists_conj_average` with `γ` yields `f`. If `f z ≠ 0`, then
   `z = γ x γ⁻¹ + γ ℓ₁ γ⁻¹ + ℓ₂`; here `γ X₀ γ⁻¹ ∈ ϖ R` (only `i > j` pieces, exponent `≥ 1`),
   `γ λ γ⁻¹ ∈ ϖ R`, `γ ℓ₁ γ⁻¹ ∈ ϖ ^ (s - m + 1) R` and `ℓ₂ ∈ ϖ ^ s R`, all inside
   `ϖ ^ (1 - h) R` for `h ≥ t`.

## Source and comparison

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, notes by
DeBacker and Sally, University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15),
Part II, §11.3 condition `C(L)` (printed p. 62) and §13 (Theorem 13.1, Lemmas 13.4–13.6, printed
pp. 63–69). Harish-Chandra conjugates by an element `γ` of the one-parameter subgroup of a
Jacobson–Morozov triple, averages `f_X ∘ Ad(k)` against a function on a compact open subgroup
using his submersion theorem, and proves Lemma 13.5 by an infinite Newton iteration. Here the
grading comes from idempotents of an order (so that `L = ϖ ^ s R` decomposes along it, the role
of his well adapted lattices), the average is the finite sum over the cosets of `L` in
`L + γ⁻¹ L γ`, and one Newton step modulo `L` replaces the iteration. The statement
proved is the conclusion of his Theorem 13.1 in the form needed by
`howeFinitenessFromAverages`.
