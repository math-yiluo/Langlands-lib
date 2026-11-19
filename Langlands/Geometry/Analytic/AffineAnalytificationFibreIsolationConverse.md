# Fibre isolation in the affine analytification forces quasi-finiteness

Author: Worker 99.

Let `K` be a complete ultrametric nontrivially normed field. Let `A` and `B`
be commutative `K`-algebras with finite polynomial presentations `P` and `Q`,
and let `f : A →ₐ[K] B`. The theorem `quasiFinite_of_forall_isolated`
assumes every `y : Space K Q` has an open set `V ∋ y` such that `z ∈ V` and
`baseMap K P Q f z = baseMap K P Q f y` imply `z = y`. It concludes that
`f.toRingHom` is quasi-finite.

## Provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), registered as `berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`, the proof of
Corollary 3.1.7, printed p.56 / PDF p.53. There the analytic fibre is
identified with the analytification of the algebraic fibre. The Lean proof
takes a different, derived route. It uses no fibre comparison, no center
surjectivity and no dimension theory. A positive-dimensional closed
algebraic fibre is exhibited directly as an infinite family of rigid points
in one fibre of `baseMap`, all inside a single compact chart.

## Seminorms from residue fields

For a `K`-algebra `A` and a field `L` algebraic over `K`:

- `map_le_max_of_root`: let `ν` be a multiplicative seminorm on `A` extending
  the norm of `K`. Suppose `ν` vanishes at `b ^ n + ∑_{j < n} a_j b ^ j`, where
  the coefficients `a_j ∈ K` have norm at most `C`. Then `ν b ≤ max 1 C`. If
  `ν b > max 1 C`, the leading term strictly dominates the other terms in the
  strong triangle inequality (`SeminormComparison.add_le_max`).
- `residueSeminorm φ` is `a ↦ spectralNorm K L (φ a)` for a `K`-algebra map
  `φ : A →ₐ[K] L`. It is a multiplicative seminorm, since Mathlib's
  `spectralMulAlgNorm` is a multiplicative norm on `L` for complete `K`. It
  extends the norm of `K` (`extendsNorm_residueSeminorm`) and vanishes exactly
  on the kernel of `φ` (`residueSeminorm_eq_zero_iff`).
- `minpoly_eq_quotient` and `minpoly_eq_of_le_ker`: maps into fields that kill
  the same maximal ideal `m` give every element the same minimal polynomial
  over `K` as its class in `A ⧸ m`.

For a finite-type `K`-algebra `B` and a maximal ideal `N` of `B`, the residue
field `B ⧸ N` is finite over `K` by Zariski's lemma
(`finite_of_finite_type_of_isJacobsonRing`). `maximalSeminorm K N hN` is
`residueSeminorm` of the quotient map `B → B ⧸ N`. It extends the norm of `K`
and vanishes exactly on `N` (`maximalSeminorm_eq_zero_iff`).

- If `N` and `N'` are maximal ideals of `B` and both contractions
  `N.comap f` and `N'.comap f` contain a maximal ideal `m` of `A`, then
  `maximalSeminorm_comp_eq` shows their seminorms agree on `f a` for every
  `a : A`. Both induced quotient maps on `A` factor through `A ⧸ m`, so the
  two images of `a` have the same minimal polynomial over `K`. The spectral
  norm depends only on that polynomial.
- `maximalSeminorm_le_of_aeval_mem`: if `β` is a root modulo `N` of a monic
  `p ∈ K[X]`, then the seminorm of `N` at `β` is at most `max 1 C`, where `C`
  bounds the norms of the lower coefficients of `p`.

## Auxiliary lemmas

- `norm_eval_le`: evaluating a multivariate polynomial at a point of the
  closed unit polydisc gives norm at most the sum of the coefficient norms.
  `norm_single_le` records that `Pi.single i₀ c` lies in this polydisc when
  `‖c‖ ≤ 1`.
- `finite_inter_fibre_of_isolated`: let `φ : X → Y` be continuous with `Y`
  Hausdorff, and `R ⊆ X` compact. If every point of `R ∩ φ ⁻¹' {x}` is isolated
  in its full fibre, then `R ∩ φ ⁻¹' {x}` is finite. That set is compact and,
  by the hypothesis, discrete.

## A bounded family of maximal ideals

`exists_maximal_family`: let `q` be a prime of a finite-type `K`-algebra `B`
that is not maximal. Then there are `b : B` and maximal ideals `F c ⊇ q`, for
`c ∈ K`, with `b - c ∈ F c`. Moreover, for each `β : B` the seminorms
`maximalSeminorm K (F c) _ β` are bounded uniformly in `c` with `‖c‖ ≤ 1`.

Noether normalization (Mathlib's `exists_integral_inj_algHom_of_fg`) gives an
injective integral map `g` from a polynomial ring in `s` variables into
`B ⧸ q`. Here `s ≠ 0`, because otherwise `B ⧸ q` would be integral over `K`
and hence a field. For `c ∈ K`, the ideal of polynomials vanishing at
`(c, 0, …, 0)` is maximal. Lying over (`Ideal.exists_ideal_over_maximal_of_isIntegral`)
gives a maximal ideal of `B ⧸ q` over it, whose preimage in `B` is `F c`. The
element `b` is a lift of the image of the first variable.

For the bound, `β` modulo `q` satisfies a monic polynomial with coefficients
in the polynomial ring. Evaluating these coefficients at `(c, 0, …, 0)` gives a
monic polynomial over `K` with a root at `β` modulo `F c`. Its lower
coefficients are bounded independently of `c` by `norm_eval_le`, and
`maximalSeminorm_le_of_aeval_mem` concludes.

## Proof of `quasiFinite_of_forall_isolated`

Suppose `f.toRingHom` is not quasi-finite. `B` is of finite type over `K`,
since `Q` presents it. By
`QuasiFiniteFibrePrimes.exists_isPrime_not_isMaximal_of_not_quasiFinite`,
there is a prime `q` of `B` that is not maximal while `q.comap f` is maximal.
Take `b` and `F` from `exists_maximal_family`. Fix `ϖ ∈ K` with
`0 < ‖ϖ‖ < 1`, and let `ν n` be the seminorm of `F (ϖ ^ n)`.

The values of `ν n` at the presentation generators of `B` are bounded
uniformly in `n`. Choose a chart level `M` whose polyradius exceeds these
bounds (`exists_radius_gt`). Then `chartPoint` places every `ν n` in the chart
`chart K Q M`. This gives points `y n` with seminorm `ν n`.

- The points are pairwise distinct. If `ν n = ν m`, then `b - ϖ ^ n` lies in
  `F (ϖ ^ m)`, as does `b - ϖ ^ m`. Hence the scalar `ϖ ^ m - ϖ ^ n` lies in the
  proper ideal `F (ϖ ^ m)`, so it is zero, and `n = m` because `‖ϖ‖ ≠ 1`.
- They lie in one fibre of `baseMap K P Q f`. Every `F (ϖ ^ n)` contains `q`,
  so its preimage under `f` contains the maximal ideal `q.comap f`. Thus all
  `ν n` agree on `f a` by `maximalSeminorm_comp_eq`. Then
  `pointSeminorm_baseMap` and `SeminormComparison.pointSeminorm_injective`
  show that all `baseMap K P Q f (y n)` are equal.

The range of `chart K Q M` is compact, `baseMap` is continuous and
`Space K P` is Hausdorff. By `finite_inter_fibre_of_isolated` and the
hypothesis, this range meets the fibre in a finite set. That set contains the
infinitely many points `y n`, a contradiction.
