# Field base change preserves ampleness of actual line bundles

This module proves the published proposition
`Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleStatement` as
`Langlands.AlgebraicGeometry.Picard.fieldBaseChangeAmple`. For arbitrary fields
`k` and `K`, any scheme morphism `b : Spec K ⟶ Spec k`, a scheme `X` with
structure morphism `p : X ⟶ Spec k`, and an ample line bundle `L` on `X`,
the actual pullback of `L` along `q = pullback.fst p b` is ample.
The theorem is universe polymorphic and has no additional premise. In
particular it includes empty schemes and arbitrary field extensions without
finiteness, perfection, separation or algebraic-closure assumptions.

The geometric argument is the affine specialization of Stacks Project
Lemma 29.38.7(2), tag [0892](https://stacks.math.columbia.edu/tag/0892), and
agrees with the relative base-change assertion of Lemma 29.38.9, tag
[0893](https://stacks.math.columbia.edu/tag/0893). The registered source is
`stacks-field-base-change-ampleness-2026-10-26`, retained as `01VG.html`,
`01VK.html`, `0892.html` and `0893.html`. Worker 689 read these originals and
their current comments on October 27, 2026. The section's separatedness
correction concerns the more general quasi-affine argument; the present
affine proof uses inverse images directly.

Both field spectra are affine, so Mathlib supplies `IsAffineHom b`.
`MorphismProperty.pullback_fst` and the instance
`isAffineHom_isStableUnderBaseChange` give `IsAffineHom q`.
Consequently `q` is quasi-compact. The compactness clause of `L.IsAmple`,
together with `QuasiCompact.compactSpace_of_compactSpace q`, proves
compactness of the fibre product.

At each point `x` of the fibre product, the second clause of `L.IsAmple`
supplies a positive exponent `n` and an actual power section `s` whose
whole generation open contains `q x` and is affine. Use the published
`LineBundle.pullbackPowSection` and
`LineBundle.sectionOpen_pullbackPowSection` from
`Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof`.
These shared helpers apply to every scheme morphism and every natural
exponent. They pull back the actual section, transport it along
`actualPullbackTensorPowIso`, and identify its entire generation open with
`q ⁻¹ᵁ L.sectionOpen s`. Their proofs already discharge the tensor comparison,
tensor-power rank-one, section-pullback and module-isomorphism compatibility
obligations. This module imports that published implementation unchanged.

Keep the same exponent and its positivity witness. The whole-open equality
gives membership of `x`, and `IsAffineOpen.preimage` along the affine morphism
`q` gives affineness of the entire generation open of the transported section.
This proves exactly both clauses of the actual published `LineBundle.IsAmple`;
the section is a section of the actual tensor power of the actual pulled-back
line bundle. The target and its imported Lean/Markdown pairs are unchanged.

The final assembly is internal derived content using the published section
transport coordinated with Worker 478 and Mathlib's affine-morphism API.
The local transparency option matches the option used by Mathlib's
affine-base-change instances and only controls proof elaboration.
