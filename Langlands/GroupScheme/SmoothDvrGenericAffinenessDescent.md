# Reduction of smooth DVR affineness to strictly henselian DVRs

`Langlands.GroupScheme.StrictHenselianSmoothDvrGenericAffinenessStatement.{u}`
is the published smooth DVR generic-affineness assertion restricted to
henselian DVRs whose residue fields are separably closed. It retains an
arbitrary specified fraction field `K` and the actual base-changed group
scheme. The source group is smooth, quasi-compact and separated, with no
connectedness or commutativity assumption.

The supporting theorem
`SmoothDvrGenericAffinenessDescent.smoothDvrGenericAffineness_of_strictHenselian`
proves that this restricted assertion implies the unchanged
`Langlands.GroupScheme.SmoothDvrGenericAffinenessStatement.{u}`.
It introduces no additional hypothesis in the resulting general criterion.
The restricted assertion itself remains an explicit premise of this reduction;
this module does not supply its geometric proof.

The restricted interface is an internal specialization for the first
reduction in Prasad and Yu, *On quasi-reductive group schemes*,
Proposition 3.1, author-preprint page 5. The proof reuses the published
strictly henselian DVR extension and faithfully flat affine-descent theorems.
The source is registered as
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.

For a DVR `R`, `strictHenselianDvrExtension` provides a faithfully flat domain
DVR algebra `A` in the same universe. It is henselian with separably closed
residue field. The proof takes `L = FractionRing A`. Faithful flatness makes
`R → A` injective; composing with `A → L` gives an injection `R → L`.
The universal property of the originally specified fraction field `K`
extends this composite to a ring map `K → L`. Thus the two actual maps
`Spec L → Spec R`, one through `Spec A` and one through `Spec K`, are equal.

`isAffine_generic_baseChange` compares the actual iterated pullbacks using
`Over.pullbackComp`. The actual generic fibre over `K` is affine by the input
hypothesis, so its pullback along `Spec L → Spec K` is affine.
The pullback comparison and the equality of the two composite maps identify
it with the actual generic fibre over `L` of the group base-changed to `A`.
No identification of `K` with a chosen fraction-ring implementation is
assumed.

Smoothness, quasi-compactness and separatedness persist under the actual
base change to `A`. The restricted assertion now makes this group affine
over `Spec A`. Both `Spec R` and `Spec A` are affine, and the base map is flat
and surjective by faithful flatness. The published
`FaithfullyFlatAffineDescent.isAffine_of_isPullback` descends affineness of
the actual pullback scheme to the original total group scheme. Since its
base is affine, its structure morphism is affine as required.
