# Smooth radical extension from an identity-component anti-affine quotient

This internal derived module works in arbitrary universe `u` over an arbitrary
extension `k ⟶ K` of algebraically closed fields. It uses the unchanged
`IsUnipotent`, `IsUnipotentRadical`, and actual `GroupScheme.baseChange`.
The ambient group `G` is smooth, with no affine, connected, quasi-compact,
finite-type, algebraicity or separability premise added to it or the extension.
The explicit extra input is supplied data
`A : AntiAffineQuotient (SmoothFieldComponent.group G)`.

`IsUnipotentRadical.baseChange_of_isAlgClosed_of_antiAffineQuotient` proves
preservation of any supplied radical `i : U ⟶ G`. The affine smooth connected
target of `A` has a represented radical by the published affine existence
theorem. Taking its full inverse image under the supplied smooth surjective
quasi-compact projection gives a represented radical of the original identity
component. The original kernel is smooth connected unipotent by anti-affineness.
The base-changed actual kernel has the same properties by the supplied quotient
base-change theorem. The smooth quotient radical-extension theorem therefore
preserves this particular component radical. The identity-component reduction
then preserves the original ambient radical. In particular, the proof does
not assume an affine source radical or use an affine unipotence base-change
theorem on a nonaffine group.

`antiAffineSmoothRadicalBaseChangeIso` constructs an actual group-scheme
isomorphism from the actual base change of `U` to the source of any supplied
radical of the extended ambient group. Its inclusion equation is
`e.hom ≫ j = baseChange.map i`. The preservation theorem supplies the full
radical predicate, and radical image uniqueness with the existing
closed-representative comparison supplies the isomorphism.

`smoothAlgebraicallyClosedUnipotentRadicalExtension_of_antiAffineQuotientExistence`
proves that `AntiAffineQuotientExistenceStatement.{u}` implies the exact published
`SmoothAlgebraicallyClosedUnipotentRadicalExtensionStatement.{u}`. Its sole
remaining premise supplies `A` for the smooth connected actual identity
component. It imposes no extra premise on that proposition's ambient group
or extension. This is a conditional reduction: anti-affine quotient existence
is a separate statement, proved as `antiAffineQuotientExistence` in
`Langlands.GroupScheme.AntiAffineQuotientExistenceProof`, so the unrestricted
proposition is not proved by this module; it is proved by combining the two, as
`smoothAlgebraicallyClosedUnipotentRadicalExtension` in
`Langlands.GroupScheme.Reductive.SmoothRadicalFieldExtensionProof`.

The provenance is the composition of the internal anti-affine fixed-vector and
quotient base-change theorems, the affine radical existence and preservation
results, the nonaffine radical-preimage theorem, and the actual smooth
identity-component comparison. No new external source assertion is used here.
