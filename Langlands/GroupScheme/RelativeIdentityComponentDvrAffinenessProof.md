# Affineness of smooth relative identity components over arbitrary DVRs

`smoothDvrAffineness` proves the exact published proposition
`Langlands.GroupScheme.RelativeIdentityComponent.SmoothDvrAffinenessStatement`
in every universe. For any DVR `R`, any smooth affine group scheme `G` over
`Spec R`, and every actual representative `i : H → G` of the all-test relative
identity component, the actual structural morphism of `H` is affine.

The proof takes the open image `U` of the supplied inclusion. The companion
`RelativeIdentityComponentFiberComparison.lean` proves that this image meets
each residue fibre in exactly its identity connected component. For the
reverse inclusion it uses the spectrum of the residue field of a total-space
point as a test scheme in the representation equivalence. The fibre inclusion
is injective, so this test meets only the relevant identity component and
therefore factors through `H`. Connected components are closed, hence `U` is
closed in each underlying fibre.

The companion `SmoothDvrAffineOpenGeometry.lean` proves affineness of any such
fibrewise closed open in a smooth affine DVR scheme. Smoothness gives local
Noetherianity and regular local stalks. The published smooth regularity theorem
and `IsRegularLocalRing.isDomain` give domain stalks, and a local algebra argument
provides irreducible open neighborhoods. An irreducible element of `R` is chosen
inside the proof. Its principal open is the generic singleton; smoothness makes
its inverse image dense. The generic intersection of `U` is closed in this
principal open, and the special intersection is closed in the whole scheme.

The companion `FibrewiseClopenAffineOpen.lean` then establishes affineness by
working locally with the inclusion `U → G`: each chosen affine chart has inverse
image equal to the whole chart, the empty open, or a principal open. Finally,
the open immersion `i` identifies the supplied `H` with `U`. Affineness
transports through this isomorphism, and the morphism from the resulting affine
scheme to `Spec R` is affine.

This is a derived proof of the affineness conclusion of Gopal Prasad and
Jiu-Kang Yu, *On quasi-reductive group schemes*, §3.5, unnumbered lemma and
proof, author-preprint PDF pp. 6–7; the arbitrary-DVR convention appears on
PDF p. 5. Registered source `prasad-yu-2006-quasi-reductive-author-preprint`,
SHA-256 `138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
The implementation uses the elementary local principal-open argument above
instead of formalizing their Proposition 3.1 or invoking their alternative
dilatation description. It adds no henselianity, perfect residue field,
connected generic fibre, existence of a representative, or uniformizer premise.
The target and its prerequisite definitions are imported unchanged.

The geometric criterion and DVR geometry were developed by Worker 410;
the all-test fibre comparison and closedness transports were developed by
Worker 1559. The local irreducibility argument reuses the method of the private
lemmas in the published
`ConnectedLocallyNoetherianDomainStalksIntegralProof.lean`, as detailed in the
geometric companion Markdown.
