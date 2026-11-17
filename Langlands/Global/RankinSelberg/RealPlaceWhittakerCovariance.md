# Actual real-place Whittaker covariance

This internal development identifies the existing real-place matrix insertion
with the actual compact insertion for an orthogonal matrix. It checks
multiplicativity of the associated adelic points and commutation with finite
adelic points.

For the actual cuspidal realization, compact translation of a vector translates
its cusp function and its global Whittaker coefficient on the right. These
identities follow from evaluation of the realized function and from the
defining integral of the Whittaker coefficient. Scalar multiplication commutes
with that total Bochner integral.

Consequently an actual real-place Whittaker restriction satisfies
`W(g (-1)) = realMinusOneScalar T v * W(g)`. The scalar-action input is the
unconditional theorem in `RealPlaceMinusOneAction`; no local-model comparison
or analytic functional equation is assumed or proved here.

The principal covariance lemma is
`IsRealPlaceWhittaker.mul_minusOne`. It allows an arbitrary additive character
`χ`; scalar homogeneity of the total Whittaker integral needs neither
integrability nor a standard-character hypothesis.

For a standard adelic character `χ`, the product of two restrictions with
characters `χ` and `χ⁻¹` is invariant under the local upper unipotent group.
The lemma `realPlacePoint_mem_unipotent` checks the actual local-to-adelic
inclusion entry by entry: the selected real component is the given upper
unitriangular matrix and every other infinite and finite component is identity.
The existing global Whittaker covariance then supplies inverse character
factors, which cancel since the character has unit modulus.

The long-Weyl inverse-transpose map carries a left unipotent translate to a
left translate by the conjugated inverse-transpose unipotent matrix.
`IsRealPlaceWhittaker.dual_product_unipotent_mul` checks this transformation
using the existing `Unfolding.dualConjGL` and proves invariance of the product
of the two dual functions. Finally,
`IsRealPlaceWhittaker.dual_mul_minusOne` proves the same scalar covariance for
the dual function, because inverse transpose fixes minus identity.

All the results retain the field universe `u`. The actual realized-function
claims assume a number field and the ambient compactness of its additive
adelic quotient, as in the Library's cuspidal realization interface.

This pair is an internal algebraic and integral calculation, rather than a
separate claim quoted from the literature.
