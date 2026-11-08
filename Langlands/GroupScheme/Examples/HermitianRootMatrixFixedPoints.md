# Fixed matrices for a nondegenerate diagonal Hermitian form

This internal construction extends the inverse-adjoint calculation to the
hyperbolic-plus-diagonal-middle form in arbitrary finite dimension over any
commutative ring. The field and finite-index universes are independent.
The additional data are actual units `w i` equal to each middle weight.
No anisotropy, characteristic, or determinant-one condition on the Gram
matrix is assumed.

`inverseGram w` has the same hyperbolic off-diagonal entries as `gram H`
and negative inverse weights in the middle. Entrywise multiplication
proves both inverse identities. `gramElement` packages these two matrices
as an actual general-linear element.

`conjugateTransposeSL` restricts conjugate transpose to determinant-one
matrices: transpose preserves determinant and the involution maps the
determinant one to one. It reverses multiplication and commutes with
inversion. Hence `inverseAdjoint` is an actual group endomorphism.
`gramConjugation` conjugates a special-linear matrix by the inverse of
`gramElement`; the determinant factors cancel without requiring the Gram
matrix itself to have determinant one.

`unitaryTwist` composes these maps. Its general-linear value is precisely
`J⁻¹ * bar(g⁻¹)ᵀ * J`. The cancellation theorem states
`bar(g)ᵀ * J * unitaryTwist(g) = J`. Cancellation in the actual general-linear
group then proves that fixedness is equivalent to the original full Gram
preservation equation. Finally `twistFixedSubgroup` is the actual fixed
subgroup inside the special-linear group, and `fixedSpecialUnitaryEquiv`
identifies it multiplicatively with the already defined determinant-one
isometry subgroup inside the general-linear group. Both directions keep
the underlying matrix unchanged.

The provenance is direct internal matrix and group algebra, extending the
existing SU3 construction while using the genuine inverse Gram matrix.
Coefficient naturality, an actual group scheme and its point comparison,
root dynamics, and the unrestricted local Kneser–Tits theorem remain
separate obligations.
