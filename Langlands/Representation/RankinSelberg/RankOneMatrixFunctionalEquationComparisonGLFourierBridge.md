# Actual Fourier exchange with weighted general linear Haar measure

This internal, derived prerequisite transfers the actual unipotent-times-matrix
Fourier exchange to the existing general linear Haar measure, with the natural
matrix-size determinant power. It proves joint integrability and an equality
of GL-outer integrals of actual unipotent averages. It does not prove compact
coefficient averaging, a gamma functional equation, or the host comparison
statement.

## Fixed field and measures

The module works over every canonical `F : PadicField.{uF} p`, with `p` prime.
It installs the canonical topology, valuation, local-field, Hausdorff,
countability and Borel structures; total disconnectedness follows from the
canonical nonarchimedean valuation. The size is `r = n + 1`, for every natural
`n`, including zero. The additive measure is exactly the published
`rectangularMeasure ν r r`, the nested product of the supplied scalar
`AdditiveHaarMeasure ν`. The other measures are the existing
`generalLinearHaar F.Carrier n` and `unipotentHaar F.Carrier n`.

Write `abv` for `normalizedAbsoluteValue F.canonicalTopologicalData`, and
`c = rectangularHaarScalar F ν n`. The GLAdditive module proves that `c` is a
positive finite NNReal and depends only on `F`, `ν`, and `n`. It is independent
of the character, tests, auxiliary measure and integrand. The factor used
below is `((c : ℝ) : ℂ)⁻¹`. The determinant weight `d(g)` is the existing
`determinantWeight abv g (n + 1 : ℕ)`, where the natural exponent is coerced
to the complex exponent. GLAdditive identifies it with the forward natural
power of the normalized absolute value of the determinant.

## Full additive measure transport

The four declarations ending in `_full` are full-measure versions of the
corresponding GLAdditive declarations:

- `integrable_generalLinearHaar_natWeight_iff_full` identifies integrability
  of `g ↦ d(g) A(g.val)` for GL Haar with integrability of `A` for the full
  supplied additive matrix measure.
- `integral_generalLinearHaar_natWeight_full` identifies the corresponding
  GL integral with `c⁻¹` times the full additive integral.
- `integrable_prod_generalLinearHaar_natWeight_iff_full` gives the same
  genuine joint-integrability equivalence for `H × GL` and `H × Mat`, for
  any measurable `H : Type uH` and s-finite auxiliary measure `μH`.
- `integral_prod_generalLinearHaar_natWeight_full` gives the product integral
  identity with this same scalar and unchanged auxiliary measure.

Their proofs rewrite the GLAdditive results with
`rectangularMeasure_restrict_generalLinear F ν r` from SingularNull. That
identity follows from genuine additive Haar nullness of the singular locus,
proved by a characteristic-polynomial, Fubini and additive-translation
argument. No test-function support premise is needed to remove this
restriction. In particular, these results do not infer invertibility from
box support. No self-duality premise is required for these four results.
The integral identities apply to Lean's totalized Bochner integrals; the
separate integrability equivalences supply their convergence criterion.

## Actual weighted orbit kernels

Use the plus entry-product rectangular Fourier transform with the supplied
`ψ` and `ν`, and write it as a hat. Let `χbar(u)` be the existing
`inverseStandardCharacter ψ n u`, `iota` the actual inverse transpose, and
`w` the unsigned reversing Weyl matrix. For `u` in the actual upper-unipotent
subgroup and `g` in the actual general linear group, the new definitions are

```text
unipotentGeneralLinearFourierDualKernel(u,g)
  = d(g) χbar(u) Φhat((iota(u) w).val * g.val) Ψ(g.val),
unipotentGeneralLinearFourierOriginalKernel(u,g)
  = d(g) χbar(u) Φ(g.val) Ψhat((w u⁻¹).val * g.val).
```

They are defined by multiplying the corresponding OrbitFourierExchange
matrix kernels by `d(g)` and pulling back by `(u,g) ↦ (u,g.val)`. Thus the
inverse character, Weyl convention, inverse transpose and multiplication
order are the existing ones; no signed representative is substituted.
The definitions themselves impose no self-duality or support premise.

`integrable_generalLinear_unipotentMatrixFourierDualKernel` assumes
`hsd : IsSelfDual ψ ν`, arbitrary Schwartz–Bruhat tests `Φ, Ψ`, and
`tsupport Ψ ⊆ RankOneBox.box F A q a`, for integers `A,q` and `0 < a`.
It proves joint integrability of the dual kernel for
`unipotentHaar.prod generalLinearHaar`. There is no invertible-support
premise on `Φ` or `Φhat`. Its proof applies the full product-integrability
equivalence to the genuine dual matrix-kernel convergence theorem.

`integrable_generalLinear_unipotentMatrixFourierOriginalKernel` assumes the
same self-duality and instead requires `tsupport Φ` to lie in the range of
the actual matrix-unit inclusion. It proves original-kernel joint
integrability, without a box premise on `Ψ`, by the corresponding original
matrix-kernel theorem and the same full product equivalence.

The two `integral_generalLinear_unipotentMatrixFourier…Kernel` declarations
express each weighted product integral as `c⁻¹` times its full additive
matrix product integral. They have no self-duality or support premise,
since they specialize the general integral-transport identity. The genuine
convergence statements above are used when applying Fubini.

## Exchange and averaged form

`generalLinear_unipotentMatrixFourier_exchange` retains both support
conditions and self-duality. It returns both weighted product
integrabilities and equality of the two weighted product integrals. The
proof first obtains the two convergence results, then uses the two exact
integral-transport identities and the already proved matrix-product Fourier
exchange. Both sides have exactly the same factor `c⁻¹`, so no additional
normalization enters the exchange.

`generalLinear_unipotentMatrixFourier_exchange_averaged` has the same
hypotheses and concludes

```text
∫ g, d(g) * (∫ u, dualMatrixKernel(u,g.val) ∂unipotentHaar) ∂generalLinearHaar
  =
∫ g, d(g) * (∫ u, originalMatrixKernel(u,g.val) ∂unipotentHaar) ∂generalLinearHaar.
```

The implementation obtains both product integrabilities and their equality
from the preceding theorem. It applies `integral_prod_symm` separately to
each side and then `integral_const_mul` to put `d(g)` outside the inner
unipotent integral. Fubini therefore rests on explicit joint convergence.
Every character is allowed by the existing `UnitaryAdditiveCharacter`
type, which bundles nontriviality; the same supplied self-dual `ν` is used
throughout, with no conductor normalization or positive-rank restriction.

## Provenance and boundary

This is source-free derived content. GLAdditive supplies the determinant
density cancellation and one fixed positive Haar scalar. SingularNull
supplies removal of the invertible-locus restriction. OrbitFourierExchange
supplies the actual matrix kernels, their genuine joint convergence and
bilinear equality, using rectangular Fourier exchange, the framed support
bound and reflection/inversion preservation of the actual unipotent Haar
measure. This module introduces only the explicit weighted pullbacks,
full-measure specializations and their Fubini consequence. It adds no
representation, coefficient-model, quotient-measure or gamma-factor premise
or conclusion. No original-literature theorem is asserted by this auxiliary
result.
