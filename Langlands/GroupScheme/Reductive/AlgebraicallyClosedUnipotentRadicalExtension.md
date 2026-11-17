# Represented affine radicals under algebraically closed extension

This derived module proves
`IsUnipotentRadical.baseChange_of_isAlgClosed_of_smooth_affine`.
Let `K/k` be an arbitrary extension of algebraically closed fields in universe
`u`, let `G` be a smooth connected affine group scheme over `k`, and let
`i : U ⟶ G` represent its unipotent radical in the published all-test sense.
Then the actual homomorphism `(GroupScheme.baseChange b).map i`, where `b`
is the spectrum map of `algebraMap k K`, represents the radical of `G_K`.
No algebraicity or separability assumption is imposed on the extension.

The proof uses the published `unipotentRadicalQuotient` to construct an
actual fppf quotient `q : G ⟶ Q`, whose full scheme-theoretic kernel has the
same subgroup functor as `i` and whose target is pseudo-reductive. The published
`algebraicallyClosedRadicalFieldExtensionStatement` gives trivial radical
for `Q_K`. Flatness and scheme surjectivity of `q` survive base change.
The actual kernel isomorphism `kernelBaseChangeIso`, together with
`SubgroupFunctor.range_baseChangeHom`, identifies the kernel of `q_K`
with the all-test range of `i_K`.

The published `unipotentRadicalExistence` supplies a radical `j` of `G_K`.
The theorem `IsUnipotentRadical.range_le_kernel_of_trivial_target` puts its
range in the kernel of `q_K`. Conversely, the range of `i_K` lies in the
range of `j` by greatestness: closedness, smoothness, connectedness,
unipotence and normality of `i` all survive this affine base change.
Equality of these ranges yields an actual source isomorphism by
`IsClosedSubgroup.sourceIsoOfRangeEq`; `IsUnipotentRadical.precomp_iso`
then transfers the radical predicate to `i_K`.

The definition `IsUnipotentRadical.baseChangeIsoOfIsAlgClosed` applies this
theorem and uniqueness of all-test ranges to construct an isomorphism from
`U_K` to the source of any supplied radical representative of `G_K`.
Its theorem `baseChangeIsoOfIsAlgClosed_hom_comp` proves that the isomorphism
followed by that representative is exactly the actual base change of `i`.

All mathematical inputs are the imported published Library declarations.
This is a focused affine prerequisite for the unrestricted smooth-ambient
extension statement; it does not assert that the ambient group in that
statement is affine or connected.
