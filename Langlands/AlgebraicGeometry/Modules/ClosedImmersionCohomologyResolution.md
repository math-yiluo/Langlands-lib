# Closed-immersion cohomology maps on compatible resolutions

This internal consequence of `ClosedImmersionCohomologyMap` and
`BaseChangeResolution` computes the canonical closed-immersion cohomology
map on compatible right resolutions. All schemes, rings and modules have
arbitrary common universe `u`.

For a closed immersion `h : Z → Y`, maps to affine bases `g` and `g'`,
and a specified base-ring square for `φ : R → S`, take actual module
sheaves `M` and `N`, right resolutions `ε : M[0] → K` and `η : N[0] → L`,
and an actual map `a : M → h_*N`. A cochain map `t : K → h_*L` must
satisfy the augmentation equation
`ε ≫ t = single₀(a) ≫ mapResolutionAugmentation(h_*, η)`.

`closedImmersionResolutionCohomologyMap` names the map from the
homology of the source sections complex to the scalar restriction of
`Hⁿ(Z, N)` obtained by taking homology of the actual sections cochain
map and then applying the scalar-restriction homology isomorphism and
the target resolution comparison. Its definition needs the target
right resolution and the cochain map, without a compatibility equation.

`resolutionComparison_closedImmersionCohomologyMap` states that the
resolution comparison for `ε` followed by the canonical cohomology map
of `a` equals the homology of `resolutionSectionsBaseChangeMap(t)`,
followed by the exact scalar-restriction homology comparison and the
scalar restriction of the resolution comparison for `η`.

The proof uses exactness of closed-immersion pushforward to ensure the
mapped target augmentation is a quasi-isomorphism. The existing inverse
pushforward comparison formula and base-ring comparison formula then
give the identity by composition. All positive higher direct images of
`N` vanish by the published closed-immersion theorem; the published
injective-pushforward acyclicity theorem supplies the other vanishing
premise. No quasi-coherence, flatness or properness is assumed.
