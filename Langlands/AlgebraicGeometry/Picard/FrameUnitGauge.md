# Changing local frames by units

Let `M` be a sheaf of modules on a scheme `X`, and let `e_i` be actual
sections on opens `T_i`. For units `a_i` on these opens, `unitGaugeFrames`
constructs the sections `a_i⁻¹ • e_i`. The definition `unitGaugeCocycle`
constructs the overlap units `a_i g_ij a_j⁻¹`, with each `a_i` restricted
under the original structure-sheaf restriction map.

The imported lemma `DualNumberThickening.isFrameOn_smul_unit` proves that
multiplication by any section unit preserves the frame property on every
smaller open in its domain. Its proof factors the frame's coefficient map
through multiplication by the restricted unit; both maps are bijective.
It has no dual-number hypotheses. The lemma `unitGaugeFrames_isFrame`
applies this existing result to the inverse units.

The transition convention is `e_j = g_ij • e_i`. The lemma
`isTransition_unitGaugeFrames` proves that the constructed units satisfy
this convention for the changed frames. It restricts the original
transition relation, expands the scalar actions, and uses the identity
`a_j⁻¹ g_ij = (a_i g_ij a_j⁻¹) a_i⁻¹` in the commutative unit group.
This transition lemma does not require the original sections to be frames.

Finally, when the original sections are frames,
`frameCocycle_unitGaugeFrames` identifies the canonical cocycle of the
changed frames with `unitGaugeCocycle` of their original canonical
cocycle. Its proof uses the two transition relations and uniqueness of
transition units for frames. No covering assumption is needed here.

The provenance is internal: this module combines the published frame
transition and uniqueness interfaces with Mathlib's unit multiplication
bijection and the direct frame-rescaling argument described above. It
constructs no total-space extension and asserts no lifting of units.
