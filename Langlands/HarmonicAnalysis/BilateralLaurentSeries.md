# Bilateral formal Laurent series and coefficientwise integration

This unit formalizes the definitions of Jacquet, Piatetski-Shapiro and
Shalika, *Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983),
Section (4.1), printed page 406. The registered source is
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed page 406 is one-based PDF page 41 of the scan. No errata are
registered for this source.

All declarations are in `Langlands.HarmonicAnalysis.BilateralLaurentSeries`,
apart from the type `Langlands.HarmonicAnalysis.BilateralLaurentSeries`
itself.

## Source definitions

JPSS (4.1)(1) defines a formal Laurent series with complex coefficients as a
formal sum `s(X) = ∑ aₘ Xᵐ` with `aₘ ∈ ℂ`, the sum extended over all
`m ∈ ℤ`. They regard the set of such series "in an obvious way" as a module,
with torsion, over `ℂ[X, X⁻¹]`.

- `BilateralLaurentSeries` is the type `ℤ → ℂ` of coefficient functions
  `m ↦ aₘ`. It is a type synonym, so that its module structure over Laurent
  polynomials is not a global instance on `ℤ → ℂ`. There is no support
  restriction: every integer-indexed coefficient function is a series.
  The complex vector space structure is that of `ℤ → ℂ`, and `ext`,
  `zero_apply`, `add_apply`, `neg_apply`, `sub_apply`, `smul_apply` and
  `sum_apply` evaluate it coefficientwise.
- `instModuleLaurentPolynomial` is the module structure over Mathlib's
  `LaurentPolynomial ℂ`, written `ℂ[T;T⁻¹]`, whose variable `T 1` plays the
  role of the source's `X`. Formal multiplication by a Laurent polynomial is
  given by finite convolution. `laurent_smul_apply` states the coefficient
  formula in Mathlib's notation for the finitely supported coefficients
  `P.coeff : ℤ →₀ ℂ`:

  ```text
  (P • a) n = ∑ k ∈ P.coeff.support, P.coeff k * a (n - k).
  ```

  The project's `Langlands.RankinSelberg.LaurentCoefficients` is an
  abbreviation for the same ring `LaurentPolynomial ℂ`, so no alternative
  Laurent polynomial ring is introduced.

In the source's second paragraph, `(Λ, dλ)` is a measure space and
`s(λ, X) = ∑ aₘ(λ) Xᵐ` has measurable coefficients. The series is
integrable when every coefficient `aₘ(λ)` is integrable, and then
`∮ s(λ, X) dλ = ∑ Xᵐ ∫ aₘ(λ) dλ`.

- `CoeffwiseIntegrable s μ` is defined for a measurable space `A`, a measure
  `μ` on `A` and a family `s : A → BilateralLaurentSeries`. It means
  `∀ n, Integrable (fun x => s x n) μ`. Mathlib's `Integrable` includes
  almost-everywhere strong measurability of each coefficient, which for
  complex-valued functions is almost-everywhere measurability. It therefore
  replaces the source's standing measurability assumption. No separate
  everywhere-measurability hypothesis is imposed.
- `coeffwiseIntegral μ s` is the series whose coefficient at `n` is the
  Bochner integral `∫ x, s x n ∂μ`; `coeffwiseIntegral_apply` records this.
  It is defined for every family. Mathlib's Bochner integral returns `0` for a
  non-integrable coefficient, so the value only has the source's meaning
  under `CoeffwiseIntegrable s μ`. The laws below assume integrability
  wherever their proofs need it.

## Derived API

The following declarations are not in the source. They implement its
"obvious" module structure and the interchange remark at the end of (4.1).

- `shift m` is the complex-linear map `a ↦ (n ↦ a (n - m))`, multiplication
  by `Xᵐ`. `shiftHom` packages the shifts as a monoid homomorphism from
  `Multiplicative ℤ` into `Module.End ℂ BilateralLaurentSeries`.
- `laurentAction` is the `ℂ`-algebra homomorphism
  `LaurentPolynomial ℂ →ₐ[ℂ] Module.End ℂ BilateralLaurentSeries` obtained
  from `shiftHom` by the universal property `AddMonoidAlgebra.lift` of the
  group algebra `ℂ[ℤ]`. The module instance is `Module.compHom` along this
  algebra map, so all module axioms are inherited from it.
  `laurent_smul_def` unfolds the action to `laurentAction P a`.
- `laurent_smul_apply` proves the convolution formula above by expanding
  `AddMonoidAlgebra.lift` as a finite sum over `P.coeff.support`.
- `T_smul_apply` is the monomial law `(T m • a) n = a (n - m)`. `C_smul` shows
  that a constant `C c` acts as the complex scalar `c`.
  `C_mul_T_smul_apply` combines the two for a monomial `C c * T m`.
- The `IsScalarTower` and `SMulCommClass` instances record compatibility of
  the complex and Laurent polynomial actions.
- `one_sub_T_one_smul_eq_zero` shows that if every coefficient of `a` is
  `1`, then `(1 - T 1) • a = 0`. This is the series `∑ Xᵐ` annihilated by
  `1 - X`, illustrating the source's remark that the module has torsion. The
  Lean statement only proves the annihilation identity.
- `coeffSeries P` is the coefficient function `n ↦ P.coeff n`.
  `ofLaurentPolynomial` packages it as a `LaurentPolynomial ℂ`-linear map
  `LaurentPolynomial ℂ →ₗ[LaurentPolynomial ℂ] BilateralLaurentSeries`.
  Linearity over Laurent polynomials is the compatibility with the module
  action. It is proved by comparing `laurent_smul_apply` with Mathlib's
  product formula `AddMonoidAlgebra.coeff_mul_apply_left`.
  `ofLaurentPolynomial_apply` evaluates the map,
  `ofLaurentPolynomial_injective` proves injectivity, and
  `ofLaurentPolynomial_mul` states
  `ofLaurentPolynomial (P * Q) = P • ofLaurentPolynomial Q`.

No multiplication of two bilateral series is defined. The source supplies
only a module over `ℂ[X, X⁻¹]`, and products of unrestricted bilateral series
need not be defined.

### One-sided support predicates

- `HasLowerBoundedSupport a` means `BddBelow {n : ℤ | a n ≠ 0}`, and
  `HasUpperBoundedSupport a` means `BddAbove {n : ℤ | a n ≠ 0}`. These are
  predicates on the actual coefficients, not restrictions on the type.
- `hasLowerBoundedSupport_iff` rewrites the first as
  `∃ N, ∀ n, n < N → a n = 0`, and `hasUpperBoundedSupport_iff` rewrites the
  second as `∃ N, ∀ n, N < n → a n = 0`.
- `hasLowerBoundedSupport_ofLaurentPolynomial` and
  `hasUpperBoundedSupport_ofLaurentPolynomial` show that Laurent polynomials
  have support bounded on both sides. Their support set is the finite set
  `P.coeff.support`.

These predicates serve later units, which will work with series supported on
one side. No support-bound extraction is proved here.

### Laws for coefficientwise integration

- `CoeffwiseIntegrable.zero`, `.add`, `.neg`, `.sub` and `.smul` show that
  integrability is preserved by the constant zero family, sums, negation,
  differences and complex scalar multiples. Each case uses the corresponding
  property of every coefficient.
- `CoeffwiseIntegrable.laurent_smul` shows that, for a fixed Laurent
  polynomial `P`, `fun x => P • s x` is coefficientwise integrable when `s`
  is. By `laurent_smul_apply`, each coefficient is the finite sum
  `∑ k ∈ P.coeff.support, P.coeff k * s x (n - k)` of integrable functions.
- `coeffwiseIntegral_zero`, `coeffwiseIntegral_neg` and
  `coeffwiseIntegral_smul` hold for every family, by the corresponding
  properties of the Bochner integral. `coeffwiseIntegral_add` and
  `coeffwiseIntegral_sub` assume that both families are coefficientwise
  integrable.
- `coeffwiseIntegral_laurent_smul` formalizes the source's remark that
  integration may be interchanged with multiplication by a polynomial in
  `X`, extended to Laurent polynomials. Under `CoeffwiseIntegrable s μ` it
  states
  `coeffwiseIntegral μ (fun x => P • s x) = P • coeffwiseIntegral μ s`.
  Each coefficient is the integral of a finite sum, so the proof uses
  integration of finite sums (`integral_finsetSum`) and constant multiples
  (`integral_const_mul`). No infinite convolution or interchange of an
  infinite sum with an integral occurs.

## Scope

This unit makes the definitions of (4.1) concrete and proves the small API
above. It proves no support-bound extraction, rational-function evaluation,
analytic continuation, determinant-slice expansion, Fourier identity or
Whittaker integral construction. The formal series attached to the
integrals of (2.4) in (4.2) are also not constructed here.
