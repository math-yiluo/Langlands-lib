# Translating a smooth chart over a strictly henselian DVR

`HenselianDvrSmoothTranslation.specialFibreTranslatingSection` constructs an
actual section of a smooth group scheme `G` over a henselian local ring `R`
whose residue field is separably closed. Given an open `U` meeting the special
fibre and a specified point `x` of that fibre, it returns a section `σ` together
with a proof that the right translate `xσ` belongs to `U`. Neither `x` nor its
image after translation is required to be rational over the residue field.
The constructor itself does not require that `R` be a DVR.

The auxiliary theorem `smooth_of_generic_and_chart` applies this construction
over a henselian DVR with separably closed residue field. For a homomorphism
`f : G → H` from a smooth group scheme, it proves that the underlying scheme
morphism is smooth if its actual base change to a specified fraction field is
smooth and its restriction to an open `U` meeting the special fibre is smooth.
There are no quasi-compactness or separatedness assumptions here, and no
smoothness, finite-type, noetherianity or affineness assumption on the target
`H`. No connectedness or perfection assumption is imposed.

This is an internal construction for the translation step in the smooth-case
proof of Prasad and Yu, *On quasi-reductive group schemes*, Proposition 3.1,
author-preprint page 5. The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
The source applies translations to a canonical affinization map; this module
isolates the smoothness consequence for any homomorphism. It asserts neither
monomorphism nor an open immersion. Those require an additional argument.

The field lemma `exists_right_translate_mem` first proves that rational
translations move any scheme point into a nonempty open of a smooth group
over a separably closed field `k`. It pulls the group and the open back to the
residue field `K` of the chosen point. Over `K` that point supplies a rational
translation, and the translated open is nonempty. The published density of
`k`-rational points after every extension of `k` supplies a ground-field point
in that open. The multiplicative pullback-point equivalence identifies this
with the required translation on the original group. Using all scheme points
in this way handles inseparable residue-field extensions.

For `exists_section_right_translate_mem`, the proof uses the actual pullback
to `IsLocalRing.ResidueField R`. Its projection has image equal to the special
fibre. The field lemma supplies a residue-field rational point giving a
suitable translation. The published
`HenselianSections.exists_section_of_smooth_of_surjective` lifts that point to
an `R`-section. Compatibility of multiplication with the pullback-point
equivalence shows that its translation has the required special-fibre value.
Classical choice packages the existence theorem as
`specialFibreTranslatingSection`.

Finally, `smooth_of_generic_and_chart` checks smoothness on an open cover of
the source. On the generic open, the assumed smooth base change composes with
the open immersion from the fraction field. On each inverse translate of
`U`, the homomorphism identity identifies the restricted morphism, up to
source and target translation isomorphisms, with the supplied smooth chart.
The section construction covers every special-fibre point; the DVR's two
points ensure that the generic open covers the rest. Zariski locality at the
source concludes the proof.
