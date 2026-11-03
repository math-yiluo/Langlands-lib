# Represented root subgroups and full-kernel centralizers under transport

This is an internal derived construction over an arbitrary base scheme `B`.
Let `i : S.toGrp ⟶ G` and `j : S'.toGrp ⟶ H` be acting commutative group
scheme maps, let `e : S ≅ S'` and `f : G ≅ H`, and supply the exact square
`i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j`.
The transported character is `characterLattice.congr e a = e.inv ≫ a`.

`subgroupTransportIso` constructs an isomorphism between supplied group schemes
representing `RelativeRoot.subgroup i a` and
`RelativeRoot.subgroup j (characterLattice.congr e a)`.
`kernelCentralizerTransportIso` does the same for the centralizers of the full
scheme-theoretic character kernels. Both constructions take the representing
inclusions and their `IsRepresentedBy` proofs as explicit inputs.

For either isomorphism `q` and the supplied inclusions `k` and `k'`, the
`hom_comp` and `inv_comp` theorems prove both inclusion squares:
`q.hom ≫ k' = k ≫ f.hom` and `q.inv ≫ k = k' ≫ f.inv`.
The `pointsEquiv` and `inv_pointsEquiv` theorems identify the action of these
scheme isomorphisms on every scheme test with the existing
`subgroupTransportEquiv` and `kernelCentralizerTransportEquiv`, respectively,
in both directions. All tests, including nonreduced tests, are retained.

When `G = H` and `f = G.innerIso g`, `subgroupTransporterConjIso` and
`kernelCentralizerTransporterConjIso` retain the same actual base point `g`
appearing in the supplied square. Their forward maps, after the inclusions,
send an ambient point `x` to `g_U * x * g_U⁻¹`; their inverse maps send `y` to
`g_U⁻¹ * y * g_U`. The general inclusion-square theorems apply to these
specializations.

The implemented proof uses the all-test comap equalities in
`CrossTorusRootTransport` and `CrossTorusKernelCentralizer`, then
`IsRepresentedBy.isoOfComap` in `RepresentedSubgroupTransport`. The latter
uses published transport of a representation along an ambient isomorphism and
uniqueness of representing subgroup schemes. Taking the images under the
supplied inclusions proves the comparison with the existing point
equivalences. The published inner-isomorphism point formulas give the
conjugation specializations. Worker 118 identified the cross-torus consumer
interface; the construction introduces no new external structure theorem.

No representability, torus existence or conjugacy, smoothness, reductivity,
relative-root realization, building, or valuation existence assertion is made.
The kernels are never replaced by their reduced or smooth parts. There is no
field, affine, splitness, root-membership, or monomorphism hypothesis on `i`
or `j`; the representing inclusions are monomorphisms as required by the
existing `IsRepresentedBy` predicate.
