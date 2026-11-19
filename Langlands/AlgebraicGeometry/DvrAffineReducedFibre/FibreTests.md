# Field tests for the affine reduced fibre theorem

Worker 594.

For an `S`-algebra `D`, write `K = FractionRing S` and
`N = integralClosure D (D ⊗[S] K)`. The definition
`integralClosureGenericFibreEquiv` gives the `K`-algebra equivalence
`K ⊗[S] N ≃ₐ[K] K ⊗[S] D`. This is an internal construction for the
affine reduced fibre theorem. It identifies the generic fibre of the
normalization with the original generic fibre.

The proof first views `D ⊗[S] K` as a localization of `N`. Elements from
the image of `nonZeroDivisors S` are units there. Any element can be written
with a numerator from `D`, whose image belongs to `N`, and a denominator
from `nonZeroDivisors S`. The inclusion of `N` is injective, so the equality
condition for localization uses the denominator `1`. The resulting
localization equivalence commutes with the two maps from `K`, since these
maps agree after composition with `algebraMap S K`. The symmetry of the
tensor product then puts `K` in the first factor on both sides.

For a domain `S`, an injective map from `S` to a field extends to `K`.
The proofs use cancellation of iterated tensor products to transport
smoothness along that extension. This gives
`smooth_genericFibre_baseChange` for an injective extension of domains
and `isReduced_tensor_integralClosure_of_injective` for field base
changes of the normalization through the generic point.

The special-fibre test uses the published geometric reducedness criterion
for quasi-compact locally finite-type schemes over a field. For a
finite-type algebra `B` over a field `k`, `isReduced_tensor_of_isReduced_tensor_perfect`
applies that criterion to `Spec B` after base change to a perfect field
extension of `k`. The affine pullback isomorphism then gives reducedness
after base change to any extension field of `k`.

For a DVR `S`, a map to a field with nonzero kernel factors through the
residue field, since the kernel is a nonzero prime. If `D` is finite type
over `S` and `N` is finite over `D`, the residue algebra of `N` is finite
type. The theorem `isReduced_tensor_integralClosure_of_residue_test`
combines the perfect-extension test for this algebra with the generic
test. It assumes that the normalization is finite and that its special
fibre over the chosen perfect field is reduced.

The distinction between the generic and special fibres and the
geometric reducedness requirement come from Conrad's appendix to
Prasad–Yu, *On quasi-reductive group schemes*, author preprint, p. 28,
Theorem A.2 and Remarks A.1 and A.3. The localization construction and
the field tests are derived auxiliary results. The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
