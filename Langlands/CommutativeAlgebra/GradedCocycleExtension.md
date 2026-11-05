# Contracting cocycles of a graded coalgebra have no negative Laurent terms

This module is pure commutative algebra over a field `k`. It is the coordinate core of
`Langlands.GroupScheme.Dynamic.exists_unipotent_conj_of_mul_inv_mem`
([`UnipotentCocharacterConjugacy`](../GroupScheme/Dynamic/UnipotentCocharacterConjugacy.md)).
That theorem conjugates two cocharacters whose quotient lies in a dynamic unipotent subgroup.
All declarations are in the namespace `Langlands.CommutativeAlgebra.GradedCocycle`.

## Setting

`B` is a commutative `k`-algebra, and `c : B →+* B[T, T⁻¹]` is a grading in the sense of the
published `GradedDVRIntegrality.IsGrading`. The coefficient `(c b).coeff n` is the
weight-`n` component of `b`. The remaining data are:

- `ε : B →ₐ[k] k`, a counit killing the components of nonzero weight;
- `Δ : B →ₐ[k] B ⊗[k] B`, satisfying the two counit laws, which are stated as equalities of
  `k`-algebra maps (`hl`, `hr` below).

A point `x : B →ₐ[k] k[t, t⁻¹]` is *contracting* when it satisfies the published
`IsContracting c ε x`. It then kills the components of negative weight and agrees with `ε` on
the components of weight `0`.

## Definitions

- `IsHomogeneous c i y`: `c y = Tⁱ y` (`AddMonoidAlgebra.single i y`). `IsHomogeneous.coeff_self`
  reads off `(c y).coeff i = y`.
- `tensorWeightSpan k c d`: the `k`-span in `B ⊗[k] B` of the pure tensors `y₁ ⊗ y₂` with
  `y₁`, `y₂` homogeneous of weights `i`, `j` and `i + j = d`.
- `polynomialPart k`: the `k`-submodule of `k[t, t⁻¹][s, s⁻¹]` of elements whose coefficient
  of `sᵐ tⁿ` vanishes whenever `m < 0` or `n < 0`.
- `innerCoeffZero k : k[t, t⁻¹][s, s⁻¹] →ₗ[k] k[s, s⁻¹]` takes the coefficient of `t⁰` in each
  `s`-coefficient (`coeff_innerCoeffZero`). It is defined coefficientwise through
  `innerCoeffZeroFun` and is only `k`-linear, not multiplicative.

## Results

`coeff_eq_zero_of_cocycle` is the main theorem. Fix `k`-algebra maps
`P Q : B → k[t, t⁻¹][s, s⁻¹]` and a function `X : B → k[t, t⁻¹][s, s⁻¹]` with these
properties:

- `(P b).coeff m = C ((x b).coeff m)`, so `P b` is `x(b)` evaluated at `s`;
- `Q b = Tʲ · x(b)` for `b` homogeneous of weight `j`, so `Q b` is `s ↦ s · x(t)`;
- `(X b).coeff m = (x b).coeff m · tᵐ`, so `X b` is `x(b)` evaluated at `st`;
- the cocycle identity `X b = productMap P Q (Δ b)`.

Assume also that `c` is a grading, that `ε` is graded, that `Δ b ∈ tensorWeightSpan k c d`
for every `b` homogeneous of weight `d`, the counit laws `hl`, `hr`, and that `x` is
contracting. Then `(x b).coeff n = 0` for every `b` and every `n < 0`.

The proof runs as follows.

- Let `e = algebraMap ∘ ε`. Define the `k`-linear map
  `D = productMap P Q - productMap P e - productMap e Q + productMap e e` on `B ⊗ B`. On pure
  tensors, `D (y₁ ⊗ y₂) = (P y₁ - e y₁)(Q y₂ - e y₂)`.
- The counit laws give `D (Δ b) = X b - P b - Q b + e b`. They enter through
  `productMap_ofId_right`, `productMap_ofId_left` and `productMap_comp_comp`.
- Strong induction on the weight `d ≥ 0` proves that `x b` has no negative terms for
  homogeneous `b`. For `d = 0` the contracting condition gives `x b = ε b`.
- For `d > 0`, `D` maps every generator of `tensorWeightSpan k c d` into `polynomialPart k`.
  - If `y₁` has weight at most `0`, then `P y₁ - e y₁ = 0`. Indeed `x y₁` is `0` (negative
    weight) or `ε y₁` (weight `0`), and `P_eq_of_eq` says that `P` only depends on `x`.
  - Likewise `Q y₂ - e y₂ = 0` when `y₂` has weight at most `0`.
  - Otherwise both weights lie in `[1, d - 1]`, and the product `(P y₁)(Tʲ x y₂)` has no
    negative exponents by the induction hypothesis (`coeff_mul_single_apply`).
- So `X b - P b - Q b + e b` lies in `polynomialPart k`. For `n < 0`, its `sⁿ tⁿ` coefficient
  is `(x b).coeff n`, since the other three terms contribute nothing there.
- A general `b` is the finite sum of its homogeneous components (`IsGrading.sum_coeff`).

`comul_mem_tensorWeightSpan` derives the weight condition on `Δ` from an intertwining identity.
Let `φL` and `φR` be `k`-algebra maps `B → (B ⊗ B)[s, s⁻¹]` with
`(φL b).coeff n = (c b).coeff n ⊗ 1` and `(φR b).coeff n = 1 ⊗ (c b).coeff n`. Assume that
`(productMap φL φR (Δ b)).coeff n = Δ ((c b).coeff n)` for all `b` and `n`. Then `Δ` maps weight
`d` into `tensorWeightSpan k c d`.

The proof shows by induction over tensors that every coefficient `d` of `productMap φL φR w`
lies in `tensorWeightSpan k c d`. On pure tensors, `AddMonoidAlgebra.coeff_mul` writes it as a
sum of terms `(c y₁)ₘ ⊗ (c y₂)ₙ` with `m + n = d`.

`algebraMap_eq_of_cocycle` sets the inner variable to `0`. Its hypotheses on `P`, `Q`, `X` are
the same as above, and it needs neither the counit laws nor contraction. Let `u : B →ₐ[k] k`
satisfy `u b = (x b).coeff 0`. Let `Qu : B →ₐ[k] k[s, s⁻¹]` satisfy `Qu b = Tʲ u(b)` for `b`
homogeneous of weight `j`. Then `algebraMap (u b) = productMap x Qu (Δ b)` for every `b`.

The proof applies the linear map `innerCoeffZero k` to the cocycle identity. For `X` this gives
`algebraMap (u b)`. The composite `innerCoeffZero k ∘ productMap P Q` equals `productMap x Qu`,
which is checked on pure tensors after decomposing the second factor into homogeneous
components.

## Provenance

This is internal infrastructure; no statement is attributed to the literature. The cocycle
argument (graded comultiplication, induction on the weight, comparison of the `sⁿ tⁿ`
coefficients) was proposed by Worker 1491 for the torus-lift step of task
`335a4eaf-9c05-43c8-9258-878ee2e39fce`, and formalized here by Worker 1515. The reduction to
linear maps on `B ⊗ B` and the use of `innerCoeffZero` for the value at `t = 0` are
formalization choices.
