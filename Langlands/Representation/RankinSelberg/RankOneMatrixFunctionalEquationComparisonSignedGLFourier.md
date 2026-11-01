# Signed orbit Fourier exchange for general linear Haar measure

This internal derived prerequisite transfers the actual signed orbit Fourier
exchange from the full additive matrix measure to the existing general linear
Haar measure. It supplies genuine joint convergence and the equality of the two
weighted product integrals, including their GL-outer averaged form. The gamma
comparison and compact averaging extraction remain separate obligations.

The field is every canonical `F : PadicField.{uF} p`, with `p` prime, and the
size is `r = n + 1`, including `n = 0`. All topology, valuation, local field,
countability and Borel instances come from `F.canonicalTopologicalData`.
The character `ψ` is any supplied nontrivial unitary additive character and
`ν` is the supplied additive Haar measure. Convergence and exchange require
`IsSelfDual ψ ν`. No conductor normalization is imposed.

Write `d(g) = determinantWeight abv g (n + 1 : ℕ)`, where `abv` is the
normalized absolute value, `χbar` for `inverseStandardCharacter ψ n`, `W`
for the actual `rankOneSignedWeyl n`, and `iota` for inverse transpose. Hats
are the plus entry-product rectangular Fourier transform for exactly `ψ,ν`.
The definitions are

```text
signedUnipotentGeneralLinearFourierDualKernel(u,g)
  = d(g) χbar(u) Φhat((iota(u) W⁻¹).val * g.val) Ψ(g.val),
signedUnipotentGeneralLinearFourierOriginalKernel(u,g)
  = d(g) χbar(u) Φ(g.val) Ψhat((W u⁻¹).val * g.val).
```

They pull back the SignedOrbitFourier kernels by `(u,g) ↦ (u,g.val)` and
multiply by the natural matrix-size determinant power. Both use the same
actual unipotent Haar and general linear Haar measures. They retain the
signed Weyl factor and its precise multiplication order.

`integrable_generalLinear_signedUnipotentMatrixFourierDualKernel` assumes
`tsupport Ψ ⊆ RankOneBox.box F A q a` for integers `A,q` and `0 < a`.
It proves integrability for the full product `unipotentHaar.prod generalLinearHaar`
without an invertible-support premise on `Φ` or its Fourier transform.
`integrable_generalLinear_signedUnipotentMatrixFourierOriginalKernel` instead
assumes invertible ambient support of `Φ`, and imposes no box premise on `Ψ`.
Each proof applies GLFourierBridge's full additive product integrability
equivalence to the corresponding genuine signed additive convergence result.

The two `integral_generalLinear_signedUnipotentMatrixFourier…Kernel` lemmas
express their total product integrals as the corresponding full additive
product integral times the same fixed inverse complex scalar
`((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹`. These identities require no
self-duality or support hypothesis. That positive finite Haar scalar depends
only on `F,ν,n`, as in GLAdditive. Removal of the singular locus restriction
uses SingularNull through GLFourierBridge; no invertibility is inferred from
box support.

`generalLinear_signedUnipotentMatrixFourier_exchange` assumes both support
conditions and self-duality. It returns both joint integrabilities and equality
of the actual weighted product integrals. The proof transports both integrals
with their identical scalar and applies SignedOrbitFourier's product exchange.

`generalLinear_signedUnipotentMatrixFourier_exchange_averaged` states the same
equality with GL as the outer variable, and the natural determinant power
outside the inner unipotent average. Its proof uses `integral_prod_symm` with
the two proved joint integrabilities, then `integral_const_mul`. Thus the
averaged equality rests on actual product convergence.

The provenance is internal. Worker 396's GLFourierBridge supplies full additive
Haar transport and its normalization scalar, while Worker 623's
SignedOrbitFourier supplies the exact signed kernels and additive exchange.
This module adapts the weighted pullback and Fubini argument of the former
to the latter. It neither assumes nor proves a matrix or rank-one gamma
functional equation, and cites no original-literature theorem.
