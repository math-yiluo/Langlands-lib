# A nonvanishing coset sum over a field of characteristic zero

This derived helper module proves the positivity input that replaces a formal degree
in the proof of the unchanged `CompactCoefficientInjectiveProjectiveStatement`. All
declarations are in `Langlands.Cohomology.SupercuspidalExtCharZero`.

## Provenance

Step 2 of the truth argument in the Markdown of
`Langlands.Cohomology.SupercuspidalExtCharZero.Statement` obtains a formal degree
from a positive definite invariant hermitian form. It uses that a sum of norms
`z z̄` with positive rational weights vanishes only if every term vanishes. Vignéras
(1996), I.7.7, proof of (ii) (printed page 59), shows that a nonzero Schur integral
`∫_G ⟨v, g ṽ⟩ ⟨w, g⁻¹ w̃⟩ dg` gives a formal degree. This module isolates the scalar
statement used in the implemented proof: one such counting sum of products of a
bi-invariant compactly supported function is nonzero. The self-convolution
argument below and the reduction to `ℂ` are derived for this project. The module does
not claim that Vignéras uses this route.

## Declarations

`cosetSum` is the sum over left cosets of `Langlands.Cohomology.SupercuspidalExtCharZero.CosetSum`.

- `cosetSum_eq_sum`: if a finite set `s` of cosets contains every coset whose
  representative gives a nonzero summand, then the coset sum equals the finite sum over
  `s`.
- `selfConvolution U f g` is `cosetSum U (fun x => f (x⁻¹ * g) * conj (f x⁻¹))`, for
  `f : G → ℂ`.
- `selfConvolution_inv`: if `f` is left `U`-invariant, then
  `selfConvolution U f g⁻¹ = conj (selfConvolution U f g)`. The proof reindexes the coset
  sum by left translation by `g⁻¹` (`cosetSum_mul_left`) and moves complex conjugation
  through the `finsum`.
- `selfConvolution_mul`: if `f` is right `U`-invariant, so is its self-convolution.
- `selfConvolution_ne_zero_mem`: a nonzero value `selfConvolution U f g` forces
  `g ∈ (tsupport f)⁻¹ * tsupport f`.

## The complex case

`exists_cosetSum_ne_zero_complex` takes an open subgroup `U` of a topological group
and `f : G → ℂ` that is left and right `U`-invariant, has compact support, and satisfies
`f 1 ≠ 0`. It concludes that there are `x y : G` with `f x⁻¹ ≠ 0` and
`cosetSum U (fun p => f (x⁻¹ * p⁻¹) * f (y⁻¹ * p)) ≠ 0`.

Write `h` for the self-convolution of `f`. All coset sums are finite sums over the finite
images in `G ⧸ U` of the compact sets `(tsupport f)⁻¹` and
`(tsupport f)⁻¹ * tsupport f`.

1. The real part of `h 1` is the sum of `normSq (f x⁻¹)` over the cosets `xU`, and the
   coset of `1` contributes `normSq (f 1) > 0`. So `h 1 ≠ 0`.
2. Suppose the conclusion fails. Expand `Q = ∑_{pU} h p⁻¹ * h p` by the finite sum
   formula for `h`. After exchanging the finite sums, `Q` is a combination, over pairs
   of cosets `xU`, `yU` with `f x⁻¹ ≠ 0` and `f y⁻¹ ≠ 0`, of the sums in the
   conclusion. So `Q = 0`.
3. By `selfConvolution_inv`, each term of `Q` is `conj (h p) * h p = normSq (h p)`.
   The coset of `1` contributes `normSq (h 1) > 0`, so the real part of `Q` is positive.
   This contradicts step 2.

## Arbitrary fields of characteristic zero

`exists_ringHom_complex`: for a finite subset `s` of a field `k` of characteristic zero,
there is a ring homomorphism `Algebra.adjoin ℚ s →+* ℂ`. The algebra is of finite type
over `ℚ`. Its quotient by a maximal ideal is a field that is a finite-dimensional
`ℚ`-vector space, because `ℚ` is a Jacobson ring (Zariski's lemma,
`finite_of_finite_type_of_isJacobsonRing`). Such a field embeds into the algebraically
closed field `ℂ` by `IsAlgClosed.lift`.

`exists_cosetSum_ne_zero` is the same conclusion as the complex case, for
`F : G → k` over any field `k` with `CharZero k`. The proof proceeds as follows.

- `F` takes finitely many values: it vanishes off a compact set and is constant on the
  left cosets of `U`, and a compact set meets finitely many of them.
- Take `s` to be the range of `F` together with `(F 1)⁻¹`, and let `τ` be a ring
  homomorphism from `A = Algebra.adjoin ℚ s` to `ℂ`. The function `f = τ ∘ F` (with
  `F` viewed in `A`) satisfies the hypotheses of the complex case. In particular
  `f 1 ≠ 0`, because `F 1` is a unit of `A`.
- The complex case gives `x` and `y`. If the sum over `k` vanished, the same finite sum,
  computed in `A` and sent through `τ`, would vanish in `ℂ`.
