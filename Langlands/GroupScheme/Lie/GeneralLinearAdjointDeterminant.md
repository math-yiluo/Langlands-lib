# The actual general-linear adjoint determinant

This internal helper proves that the actual rational character
`Lie.adjointDeterminantCharacter` of `GeneralLinear.groupScheme n k` is zero
for every characteristic-zero field `k` and every finite index type `n`.
The field universe is arbitrary; the finite index type has the same universe
convention as the existing general-linear scheme. Empty index types are included.
No additional geometric hypothesis is supplied: the existing affine and smooth
instances for this group scheme are installed locally.

`adjoint_scalar_eq_id` first proves that every scalar matrix acts as the identity
on the actual dual-number Lie kernel, over any field. The published linear
coordinates `DualNumber.pointKernelLinearEquiv` identify the action with
`X ↦ z X z⁻¹`. Scalar matrices commute with every matrix, so cancellation gives
`X`. The proof uses the actual adjoint map and its proved coordinate formula.

`adjointDeterminantCharacter_eq_zero` applies the existing classification
`exists_characterOnAffineMatrices_power` to the actual adjoint determinant.
That classification supplies one integer `m` such that the character is
`det^m` on every affine test algebra, including nonreduced algebras.
For a nonempty index type, evaluate on the scalar matrix with value two over
`k`. The scalar-action lemma makes its adjoint determinant one, giving
`2^(card(n)*m) = 1` in `k`. Injectivity of the rational field map transports
this equality to `ℚ`. Since the positive rational number two has no nonzero
integer power equal to one, `card(n)*m = 0`; nonempty finite cardinality gives
`m = 0`. For an empty index type, every general-linear point is the identity,
so every character already has value one. In both cases the affine-point
extensionality theorem proves equality of the original scheme character with
the zero character.

This is an internal deduction from proved Library character classification,
actual Lie coordinates and elementary field identities. It asserts no
modular-character comparison, Haar invariance, integrability or local-unitarity
conclusion on its own. Those analytic steps are implemented separately.
