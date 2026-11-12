# Counting points on hyperplane sections over a finite field

Author: Worker 5132.

This helper module holds the elementary counting for the hyperplane-slicing step
`FamilyLangWeilSlicingStatement` of the uniform Lang–Weil estimate. It involves no geometry. An
affine hyperplane of `κⁿ`, for a finite field `κ`, is given by parameters
`α : Option (Fin n) → κ`, with constant term `α none` and linear coefficients `α (some i)`. The
hyperplane is `α none + ∑ᵢ α (some i) xᵢ = 0`.

## Provenance

Provenance: internal. These are the counting steps of the induction in Serge Lang and André
Weil, *Number of points of varieties in finite fields* (Amer. J. Math. 76 (1954), registered
source `lang-weil-1954-number-of-points`, printed pp. 822–823): a double count of the pairs
(point, hyperplane through it), a bound on the exceptional hyperplanes, and a comparison of the
two evaluations. The Schwartz–Zippel bound in Lean replaces Lang–Weil's Lemma 2 (printed p. 821)
for the exceptional parameters, and a linear-algebra count handles the hyperplanes that contain
the whole variety. The statements are formulated for this proof and are not quoted from a
source.

## Declarations

- `card_filter_hyperplane_through n w`: for a fixed `w : Fin n → κ`, the parameters with nonzero
  linear part whose hyperplane passes through `w` number `#κ ^ n - 1`. Proof: such a parameter
  is determined by its nonzero linear part `a`, with constant term `-∑ aᵢ wᵢ` (`card_nbij'`).
- `sum_card_filter_hyperplane n v`: double counting. For a finite family `v : ι → (Fin n → κ)`,
  the sum over all parameters with nonzero linear part of the number of `x` with `v x` on the
  hyperplane equals `#ι · (#κ ^ n - 1)`. Proof: exchange the two sums (`sum_comm`) and apply the
  previous lemma to each `x`.
- `card_filter_eval_eq_zero_le hp m hσ`: the Schwartz–Zippel bound over a finite field. A
  nonzero polynomial `p` in `m + 1` variables, indexed by any finite type `σ`, vanishes at no
  more than `totalDegree p · #κ ^ m` points of `κ^σ`. Proof: rename the variables to
  `Fin (m + 1)` and apply Mathlib's `MvPolynomial.schwartz_zippel_totalDegree` with `S = κ`.
- `card_filter_mem_ideal_mul_le I hI n g i₀ hi₀`: let `T` be a `κ`-algebra, `I ≠ ⊤` an ideal and
  `g : Fin n → T`, and suppose `g i₀ - c ∉ I` for every constant `c`. Count the parameters with
  nonzero linear part such that `α none + ∑ᵢ α (some i) • gᵢ ∈ I`. Then
  `(count + 1) · #κ ≤ #κ ^ n`. Proof: these parameters, together with `0`, lie in the kernel of
  the `κ`-linear map `L : κ^{n+1} → T ⧸ I`, `α ↦ α none + ∑ α (some i) gᵢ mod I`. The images of
  the constant `1` and of the coordinate `g i₀` are linearly independent: `1 ∉ I` because
  `I ≠ ⊤`, and `g i₀` is not congruent to a constant. So `L` has rank at least `2`, its kernel
  has dimension at most `n - 1`, and the kernel has at most `#κ ^ (n - 1)` elements.
- `abs_sub_pow_le_of_slices`: the estimate on real numbers. A parameter set `Λ` of size
  `P Q - Q` (`P` stands for `Q ^ n`, `Q = #κ ≥ 2`) splits into three disjoint parts:
  - `Λc`, the parameters whose slice count `Nα` equals the total `N`; they satisfy
    `(#Λc + 1) Q ≤ P`;
  - `Λb`, at most `D P` exceptional parameters, with `0 ≤ Nα ≤ C₂ Q ^ (d + 1)`;
  - the rest, with `|Nα - Q ^ (d + 1)| ≤ C₁ Q ^ (d + 1 - 1/2)`.

  If `∑_{α ∈ Λ} Nα = N (P - 1)`, then
  `|N - Q ^ (d + 2)| ≤ 2 (2 + D + C₁ + D C₂) Q ^ (d + 2 - 1/2)`. Proof: split the sum into the
  three parts. This gives the identity
  `(N - Q^{d+2}) (P - 1 - #Λc) = S_b - (#Λc + #Λb) Q^{d+1} + #Λc Q^{d+2} + E`,
  where `E` is the total error over the good parameters. Bound each right-hand term by a
  multiple of `P Q^{d+1} Q^{1/2}`, and divide by `P - 1 - #Λc ≥ P/2`.
