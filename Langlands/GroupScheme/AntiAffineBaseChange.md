# Field base change of anti-affine groups and supplied quotients

This derived module works over arbitrary fields `k` and `L` in the same
arbitrary universe `u`. Every extension parameter `φ : k →+* L` is an
arbitrary field homomorphism, and every base change is the actual
`GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))`.

`IsAntiAffine.of_iso` transports anti-affineness along an actual group-scheme
isomorphism. `IsAntiAffine.baseChange` preserves it when the source scheme is
compact and quasi-separated. The published flat-base-change pushout for global
sections carries the structure-map isomorphism to the pullback structure map.
`IsAntiAffine.baseChange_of_smooth_connected` obtains these two source
properties from `quasiCompact_of_smooth_connected` and field separatedness.
The auxiliary `connectedSpace_baseChange_of_smooth_connected` likewise derives
quasi-compactness before applying geometric connectedness of connected field
groups. Neither of these smooth connected specializations assumes affineness.

`IsAffinization.baseChange` starts with an actual homomorphism `q : G ⟶ Q`
whose target is affine and whose global-section map is an isomorphism. Assuming
only compactness and quasi-separatedness of the source, it proves the same
predicate for the actual base-changed homomorphism. Affineness is stable under
base change. The flat-global-sections pushout squares for `G` and `Q`, together
with naturality of `q`, form a stacked pushout diagram. Cancellation of the
square for `Q` shows that the new global-section map is a pushout of the old
one, hence an isomorphism. Thus the result retains the specified canonical
scheme affinization meaning of `IsAffinization`, including its `targetIso` and
`comp_targetIso` consequences.

For supplied data `A : AntiAffineQuotient G`,
`AntiAffineQuotient.baseChange A φ` constructs quotient data for the actual
base-changed source. Its group is the actual base change of `A.group`, and its
projection is the actual base change of `A.projection`. This construction adds
no hypotheses on `G`: its compactness follows from the supplied quasi-compact
projection to the affine target, and field separatedness supplies
quasi-separatedness. The preceding affinization theorem applies. Target
smoothness and projection smoothness, surjectivity and quasi-compactness are
preserved by pullback. Smooth connected field-group geometry gives
connectedness of the new target.

`antiAffine_kernel_baseChange` first applies anti-affine base change to the
original smooth connected kernel, then transports it through
`kernelBaseChangeIso`. The same actual kernel comparison transports smoothness
and connectedness in the quotient construction. These assertions concern the
full scheme-theoretic kernel, rather than just rational points.
`hasSmoothConnectedUnipotentKernel` and
`hasSmoothConnectedUnipotentKernel_baseChange` provide the corresponding
unchanged Library predicates for the original and the base-changed projection;
unipotence follows from the anti-affine fixed-vector theorem.

The provenance is entirely internal: the module combines the flat-global-sections
pushout theorem, field separatedness, the smooth field component's
quasi-compactness theorem, geometric connectedness, and the actual kernel
base-change comparison. It constructs base change of supplied quotient data.
Existence of such data and the host radical-extension theorem remain separate
proof obligations.
