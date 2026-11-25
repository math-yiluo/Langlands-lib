# Star-compatible torus comparisons have inner discrepancy

This supporting module is internal to the proof of
`Langlands.GroupScheme.InnerFormStarActionStatement`. Its provenance is the
composition of the published star-action projection, actual torus-compatible
root-data transport, pinned Weyl innerness, adjoint quotient transport, and
finite-Galois discrepancy lemmas described below.

For two affine groups of locally finite type over a field, supplied Galois
pinning data over an extension, and a comparison of their base-changed groups,
`Comparison` records an actual group isomorphism, an isomorphism of the chosen
split maximal tori, and the commuting inclusion square.
`Comparison.ofPinnedIso` forgets the extra conditions on a pinned isomorphism.
`torusIso` writes its torus comparison with explicit base-change endpoints.
`twistIso`, `twistTorusIso` and `inclusion_comp_twistIso` reuse the published
constructions in `InnerFormStarForward`: the discrepancy on the target group
is the comparison inverse followed by its canonical Galois pullback, and it
normalizes the chosen target torus through the corresponding torus discrepancy.

`galoisAction_difference_mem` assumes that a based root-datum equivalence
intertwines the two star actions at a field automorphism. Compatibility of
based projection with conjugation gives equality of the based projections of
the two ordinary Galois actions. Their quotient therefore belongs to the
kernel of that projection, which is the abstract Weyl group.

`characterAut_twistTorusIso_eq` identifies the character action of the torus
discrepancy with that quotient of ordinary actions. It constructs the full
root-datum automorphism induced by the inverse group and torus discrepancies,
then applies the published `InnerFormStarForward.galoisAction_eq_twist_mul`.
The character map of this root automorphism is precisely inverse character
pullback along the torus discrepancy, which is the convention of
`characterAut`. Cancelling the conjugated source action proves the formula.
`characterAut_twistTorusIso_mem_weylImage` combines this identity with the
previous Weyl membership and the published inclusion of the abstract Weyl
action into the actual normalizer image.

`hasInnerDiscrepancy` assumes a finite Galois extension, a supplied adjoint
quotient of the source group, and a root equivalence matching inverse character
pullback along the comparison, preserving the bases, and intertwining every
finite star action. It concludes the full all-test inner-discrepancy property
of `LocalGroupIso.ofBaseChangeIso` for the supplied source adjoint action.
The proof constructs an adjoint quotient of the target base change. For each
Galois automorphism, `SplitPinning.exists_adjointPoint_of_weylImage` represents
the target discrepancy by an actual point of that adjoint quotient. The
isomorphism of adjoint quotients induced by the group comparison transports
this point back to the base change of the supplied source quotient;
`IsAdjointQuotient.basePointIso_trans` checks its action. Finally,
`IsAdjointQuotient.hasInnerDiscrepancy_of_galois_baseChange` promotes these
pointwise finite-Galois identities to the required property on every scheme
and every further test map. No extra quotient, centre, or rational-point
hypothesis is imposed on `InnerFormStarActionStatement`.
