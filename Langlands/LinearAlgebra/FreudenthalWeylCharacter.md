# The Weyl character formula from Freudenthal's recursion

Module `Langlands.LinearAlgebra.FreudenthalWeylCharacter`, namespace
`Langlands.LinearAlgebra.WeylCharacter`.

Throughout, `M` is an abelian group and `ℤ[M]` is the group ring
`AddMonoidAlgebra ℤ M`, with `e^μ = single μ 1`. In the second half,
`P : RootPairing ι ℤ M N` is a root pairing over `ℤ` with a base `b`, and
`F : M →ₗ[ℤ] M →ₗ[ℤ] ℚ` is a `ℚ`-valued `ℤ`-bilinear form on `M`. The alternant
`J(ν) = alternant P ν`, the denominator `e^ρ ∏_{α>0} (1 - e^{-α})`
(`denominator b ρ`), `posRoots b`, `IsAlternating`, `IsBelow`, the Weyl
denominator identity `denominator_eq_alternant` and the uniqueness lemma
`eq_alternant_of_isBelow` come from the companion module
`Langlands.LinearAlgebra.WeylDenominatorIdentity`. `IsStrictlyDominant` and
`pairing_rho_eq_one` come from `Langlands.LinearAlgebra.SimpleReflectionWords`.
`reflectionGroup`, `positiveCone` and `IsDominant` are the Library's
definitions in `Langlands.LinearAlgebra.DominantTriangularInvariants`.

The main result, `alternant_mul_ofCoeff_eq`, is purely combinatorial. Suppose
an integer-valued, finitely supported function `c` on `M` satisfies
Freudenthal's multiplicity recursion for a symmetric, reflection-invariant,
positive definite form `F`. Suppose also that `c` is reflection invariant,
that `c(λ) = 1`, and that the support of `c` lies below `λ`. Then
`J(ρ) · ∑_μ c(μ) e^μ = J(λ + ρ)`. In the project this result turns
Freudenthal's formula into the Weyl character formula.

## Provenance

This is the project's own derivation, not a transcription of a single source.
The recursion in the hypothesis `hfreud` is Freudenthal's multiplicity formula
(Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9,
§22.3; Freudenthal, Indag. Math. 16 (1954)), written with the sum over all
roots and without `ρ`. The conclusion is the identity in the Weyl character
formula (Milne, *Algebraic Groups* (2017), Theorem 22.52). The argument is a
uniqueness argument. A Laplacian on `ℤ[M]` multiplies `e^μ` by `F(μ, μ)`. The
recursion says that the product `D χ` of the Weyl denominator `D` and
`χ = ∑ c(μ) e^μ` is an eigenvector of this Laplacian with eigenvalue
`F(λ + ρ, λ + ρ)`. The product `D χ` is alternating and lies below `λ + ρ`.
The only strictly dominant `ν ≤ λ + ρ` with `F(ν, ν) = F(λ + ρ, λ + ρ)` is
`ν = λ + ρ`. So the uniqueness lemma of the companion module identifies `D χ`
with `J(λ + ρ)`. The Weyl denominator identity `D = J(ρ)` then gives the
result. The algebraic identities below make the eigenvector computation
precise. They are stated for convolutions with arbitrary functions
`M → ℚ`, because the infinite root-string sums are not elements of `ℤ[M]`.

## Convolution of `ℤ[M]` with functions

- `conv f h` is `(f ⋆ h)(ν) = ∑_κ f(κ) h(ν - κ)` for `f ∈ ℤ[M]` and
  `h : M → ℚ`. It is a finite sum over the support of `f`.
- Linearity: `conv_zero_left`, `conv_add_left`, `conv_sub_left`,
  `conv_zero_right`, `conv_add_right`, `conv_sub_right`, `conv_smul_right`,
  `conv_sum_right`. Also `conv_single` (`(r e^a ⋆ h)(ν) = r h(ν - a)`) and
  `conv_one`.
- `conv_mul`: `(f g) ⋆ h = f ⋆ (g ⋆ h)`. The proof is induction on `f` and `g`
  (`AddMonoidAlgebra.induction_linear`) and the case of two monomials.
  `conv_comm_mul` follows from commutativity of `ℤ[M]`.
- `conv_coeff`: convolving with the coefficient function of `g ∈ ℤ[M]` gives
  the coefficient function of `f g`.
- `conv_one_sub_single`, `conv_one_add_single`:
  `((1 ∓ e^{-α}) ⋆ h)(ν) = h(ν) ∓ h(ν + α)`.

## Root-string sums

- `finsum_nat_eq_zero_add`: for a finitely supported `f : ℕ → ℚ`,
  `∑ᶠ j, f j = f 0 + ∑ᶠ j, f (j + 1)`.
- `stringSum α T μ` is `∑ᶠ_{j ≥ 0} T(μ + (j + 1) α)`, that is
  `∑_{j ≥ 1} T(μ + j α)`.
- `stringSum_eq`: if `n ↦ n α` is injective on `ℕ` and `T` is finitely
  supported, then `S(α, T)(μ) = T(μ + α) + S(α, T)(μ + α)`.

## The Laplacian, derivatives and the bilinear term

For the form `F`:

- `lap F h` is `ν ↦ F(ν, ν) h(ν)` (the Laplacian, `e^μ ↦ F(μ, μ) e^μ`).
- `der F x h` is `ν ↦ F(x, ν) h(ν)` (the derivative `∂_x`, `e^μ ↦ F(x, μ) e^μ`).
- `bil F f h` is `B(f, h)(ν) = ∑_κ f(κ) F(κ, ν - κ) h(ν - κ)`, the term
  `⟨∇f, ∇h⟩`. Its linearity lemmas are `bil_zero_left`, `bil_add_left` and
  `bil_sub_left`. Also `bil_single` (`B(r e^a, h) = r e^a ⋆ ∂_a h`), `bil_one`
  (`B(1, h) = 0`) and `bil_one_sub_single`
  (`B(1 - e^{-α}, h) = e^{-α} ⋆ ∂_α h`).
- `der_neg`, `der_add`, `der_sum`, `der_nsmul`: `∂_x` is additive in `x`.
- `bil_mul` (Leibniz rule): `B(f g, h) = f ⋆ B(g, h) + g ⋆ B(f, h)`. It is
  checked on monomials, where it is bilinearity of `F` in the first argument.
- `lap_conv` (product rule): if `F` is symmetric and `F(κ, κ) = r` for every
  `κ` in the support of `f`, then
  `Δ(f ⋆ h) = r (f ⋆ h) + f ⋆ Δh + 2 B(f, h)`. Each term comes from expanding
  `F(κ + (ν - κ), κ + (ν - κ))`.

## Telescoping along root strings

`F` is symmetric in this section.

- `conv_one_sub_single_stringSum`: let `α` have injective nonnegative
  multiples, as does `-α`, and let `χ` be finitely supported. Put
  `S_α = S(α, κ ↦ F(κ, α) χ(κ))` and `S_{-α} = S(-α, κ ↦ F(κ, -α) χ(κ))`. Then
  `(1 - e^{-α}) ⋆ (S_α + S_{-α}) = (1 + e^{-α}) ⋆ ∂_α χ`. At `ν`, the left side
  is `S_α(ν) + S_{-α}(ν) - S_α(ν + α) - S_{-α}(ν + α)`. By `stringSum_eq`,
  `S_α(ν) - S_α(ν + α) = F(ν + α, α) χ(ν + α)` and
  `S_{-α}(ν) - S_{-α}(ν + α) = F(ν, α) χ(ν)`. Their sum is the right side.
- `two_smul_conv_single_add`:
  `2 (e^{-α} ⋆ d) + (1 - e^{-α}) ⋆ d = (1 + e^{-α}) ⋆ d`.
- `two_smul_bil_prod`: let `Q = ∏_{i ∈ s} (1 - e^{-α_i})` for a finite family.
  Suppose `(1 - e^{-α_i}) ⋆ U_i = (1 + e^{-α_i}) ⋆ ∂_{α_i} h` for every
  `i ∈ s`. Then `2 B(Q, h) + Q ⋆ ∑_i ∂_{α_i} h = Q ⋆ ∑_i U_i`. The proof is
  induction on `s`, using `bil_mul`, `bil_one_sub_single`, the hypothesis for
  the new factor and `two_smul_conv_single_add`.
- `two_smul_bil_denominator`: if moreover `2 ρ = ∑_{i ∈ s} α_i`, then
  `2 B(e^ρ Q, h) = e^ρ Q ⋆ ∑_i U_i`. The Leibniz rule gives
  `B(e^ρ Q, h) = e^ρ ⋆ B(Q, h) + Q ⋆ e^ρ ⋆ ∂_ρ h`, and
  `2 ∂_ρ = ∑_i ∂_{α_i}`.

## Invariant forms and the reflection group

- `apply_eq_of_mem_reflectionGroup`: a function invariant under every
  reflection is invariant under the reflection group. The proof is
  `Subgroup.closure_induction`. `form_apply_eq_of_mem_reflectionGroup` is the
  same statement for a form.
- `form_root_mul_pairing`: for a reflection-invariant form,
  `F(α_i, α_i) ⟨x, α_i^∨⟩ = 2 F(α_i, x)`. Expand
  `F(s_i α_i, s_i x) = F(α_i, x)` using `s_i α_i = -α_i`.
- `form_nonneg_of_mem_positiveCone`: let `F` be symmetric,
  reflection-invariant and positive definite (`0 < F(x, x)` for `x ≠ 0`). If
  `ν` is dominant and `d` lies in the positive cone, then `0 ≤ F(ν, d)`. On a
  simple root this is `2 F(ν, α_a) = F(α_a, α_a) ⟨ν, α_a^∨⟩ ≥ 0`. The general
  case follows by additivity.
- `form_lt_of_mem_positiveCone`: under the same hypotheses, if `d ≠ 0` then
  `F(ν, ν) < F(ν + d, ν + d)`. This adapts the argument of the Library's
  `rootForm_lt_of_dominant` to an arbitrary such form `F`.
- `exists_eq_of_coeff_alternant_ne_zero`: every element of the support of
  `J(ν)` has the form `w ν` with `w ∈ W`.

## Roots

- `nsmul_root_injective`, `nsmul_neg_root_injective`: `n ↦ n α_i` and
  `n ↦ n (-α_i)` are injective on `ℕ`. Pair with `α_i^∨`, using
  `⟨α_i, α_i^∨⟩ = 2`.
- `isDominant_of_invariant`: let `c : M →₀ ℤ` be reflection invariant, with
  `c(λ) ≠ 0` and support below `λ`. Then `λ` is dominant. Since
  `c(s_a λ) = c(λ) ≠ 0`, the element `λ - s_a λ = ⟨λ, α_a^∨⟩ α_a` lies in the
  positive cone. If `⟨λ, α_a^∨⟩ < 0`, its negative also lies in the cone. So
  it is `0` (`eq_zero_of_mem_positiveCone_of_neg_mem`), which contradicts
  `⟨α_a, α_a^∨⟩ = 2`.
- `negIdx P i` is the index `s_i(i)` of the root `-α_i` (`root_negIdx`,
  `negIdx_negIdx`).
- `finsum_posRoots`: the `finsum` over indices with positive root equals the
  sum over `posRoots b`.
- `sum_eq_sum_posRoots_add_negIdx`: a sum over all roots is the sum over the
  positive roots `i` of `V(i) + V(negIdx i)`. Every root is positive or
  negative and not both (`root_mem_or_neg_mem`, `neg_root_notMem_of_mem`).

## The main theorem

`alternant_mul_ofCoeff_eq` assumes that `ι` is a `Fintype`, that `P` is
reduced and that `M` is free of finite rank over `ℤ`. Its hypotheses are:

- `F` symmetric (`hFs`), invariant under every reflection `P.reflection i`
  (`hF`) and positive definite (`hpos`);
- `2 • ρ = ∑ᶠ (i) (_ : α_i ∈ positiveCone P b), α_i` (`hρ`);
- `c : M →₀ ℤ` reflection invariant (`hinv`), with `c(λ) = 1` (`hlam`) and
  `λ - μ` in the positive cone whenever `c(μ) ≠ 0` (`hbelow`);
- for every `μ`, Freudenthal's recursion (`hfreud`):

```text
(F(λ, λ) + ∑ᶠ (i) (_ : α_i ∈ positiveCone P b), F(λ, α_i) - F(μ, μ)) c(μ)
  = ∑ᶠ (i : ι) (j : ℕ), F(μ + (j + 1) α_i, α_i) c(μ + (j + 1) α_i).
```

Its conclusion is `alternant P ρ * ofCoeff c = alternant P (lam + ρ)`.

The proof, with `χ(μ) = c(μ)` and `D = e^ρ ∏_{α > 0} (1 - e^{-α})`:

1. For a positive root `α_i`, put `V_i = S(α_i, κ ↦ F(κ, α_i) χ(κ))` and
   `U_i = V_i + V_{negIdx i}`. Then `V_{negIdx i}` is the string sum for
   `-α_i`, so `conv_one_sub_single_stringSum` gives
   `(1 - e^{-α_i}) ⋆ U_i = (1 + e^{-α_i}) ⋆ ∂_{α_i} χ`.
2. Let `c₀ = F(λ, λ) + ∑_{α > 0} F(λ, α)`. Regrouping the sum over all roots
   in `hfreud` by `sum_eq_sum_posRoots_add_negIdx` gives
   `∑_{α_i > 0} U_i = c₀ χ - Δχ`.
3. By the Weyl denominator identity, `D = J(ρ)`. Its support consists of
   elements `w ρ`, so `F(κ, κ) = F(ρ, ρ)` on it. `lap_conv` and
   `two_smul_bil_denominator` (with `2 ρ = ∑_{α>0} α`) then give
   `Δ(D ⋆ χ) = F(ρ, ρ) D ⋆ χ + D ⋆ Δχ + D ⋆ (c₀ χ - Δχ) = (F(ρ, ρ) + c₀) D ⋆ χ`.
4. `F(ρ, ρ) + c₀ = F(λ + ρ, λ + ρ)`, since `∑_{α>0} F(λ, α) = 2 F(λ, ρ)`.
   With `g = D · ∑ c(μ) e^μ` (`conv_coeff`), this reads
   `F(ν, ν) g(ν) = F(λ + ρ, λ + ρ) g(ν)` for every `ν`.
5. `g` is alternating: `D` is alternating (`isAlternating_denominator`) and
   `∑ c(μ) e^μ` is `W`-invariant by `hinv`. `g` lies below `λ + ρ` with
   coefficient `1` there (`IsBelow.mul`, `IsBelow.coeff_mul`). By
   `isDominant_of_invariant` and `⟨ρ, α_a^∨⟩ = 1`, `λ + ρ` is strictly
   dominant.
6. Let `ν` be strictly dominant with `g(ν) ≠ 0`. Then `λ + ρ - ν` lies in the
   positive cone. If `ν ≠ λ + ρ`, then `form_lt_of_mem_positiveCone` gives
   `F(ν, ν) < F(λ + ρ, λ + ρ)`, which contradicts step 4. So `ν = λ + ρ`, and
   `eq_alternant_of_isBelow` gives `g = J(λ + ρ)`. Finally replace `D` by
   `J(ρ)`.
