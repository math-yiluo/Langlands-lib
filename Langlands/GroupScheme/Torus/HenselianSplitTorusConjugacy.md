# Integral conjugacy of closed split tori over a Henselian ring

This internal module assembles actual integral conjugacy from published
specialization, residue conjugacy, and Henselian transporter results. It is a
derived construction, using `HenselianSplitRank`,
`SmoothMaximalSplitTorusConjugacyProof`, `HenselianNormalizerLifting`, and the
extension of isomorphisms in `FieldFibreIsomorphism`. It asserts no new
transcription from the literature.

All types use an arbitrary common universe `u`, and both field
characteristics are allowed. For the existence constructions, `R` is a
commutative Henselian local ring and `k` is a field with a surjective
`R`-algebra map. The actual ambient group scheme `G` over `Spec R` is smooth
and affine, and its actual fibre over this presentation of `Spec k` has
connected underlying space. The supplied maps are `i : T.toGrp → G` and
`i' : T'.toGrp → G`, where `T` and `T'` are split commutative tori over `R`.

`SplitTorusConjugator i i'` records an actual integral section `g` of `G`, an
actual isomorphism `e : T ≅ T'`, and the all-test transporter equation between
`groupHom e.hom ≫ i'` and `i`. This data structure itself needs only the
commutative base ring and the two commutative source group schemes, without
splitting or smoothness hypotheses. Its theorem `SplitTorusConjugator.comm`
proves the equality of actual group-scheme homomorphisms

    i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ i'.

Thus `g` conjugates the image of `i` to the image of `i'`, with the displayed
orientation. In `PointwiseSchemeAction`, `isTransporter_of_comp_innerIso_eq`
and `IsTransporter.comp_innerIso_eq` prove the two conversions between this
homomorphism equality and the all-test transporter equation for two maps from
the same arbitrary group. Their proofs test the homomorphism equality on
arbitrary schemes, identify the restriction of the section with its constant
point, and use the inner-conjugation formula and multiplication by the inverse.

`exists_splitTorusConjugator_of_residue` assumes that both pulled-back maps
are maximal split tori in `G_k`. It proves that the data structure is inhabited.
It does not need generic maximality or a fraction field for this version.
`henselianSplitTorusConjugatorOfResidue` chooses those data by classical choice.
The proof is as follows:

1. `smoothMaximalSplitTorusConjugacy` gives an actual residue section `g₀` and
   an actual isomorphism `e₀` of the residue tori, with
   `i_k ≫ int(g₀) = e₀.hom ≫ i'_k`.
2. `IsSplitTorus.iso_fieldBaseChange_surjective` extends that isomorphism to
   an actual integral isomorphism `e`, with exactly the prescribed pullback.
   The residue equation is therefore the all-test transporter equation for
   the pullbacks of `groupHom e.hom ≫ i'` and `i`.
3. `IsTransporter.baseChangePointsEquiv` projects this residue transporter
   to an actual `Spec k` point of `G` over `Spec R`.
   `exists_henselian_transporter_of_split` lifts it to an actual integral
   section with the same all-test equation. The proof retains the section,
   integral isomorphism, and transporter equation. Although the published
   lifting theorem also gives exact residue recovery, this chosen data
   structure does not record a prescribed residue point.

`henselianSplitTorusConjugator` replaces the residue maximality assumptions
by generic-style field-fibre assumptions. Here `K` is any additional field with
an `R`-algebra structure. The hypotheses are that `G_K` is connected reductive,
`i` and `i'` are closed integral inclusions, and both pulled-back maps to `K`
are maximal split tori. Applying
`isMaximalSplitTorus_residue_of_generic` separately to the two inclusions
proves residue maximality, so the preceding construction applies. The torus
maps used in these hypotheses are the actual pullbacks, before any optional
identification of the ambient field fibre. No domain, DVR, fraction-field,
reductivity of the whole integral model, or reductivity of the residue fibre
is required.

For a supplied `IntegralModel M`, the recorded all-test equation can be passed
directly to the separate `M.genericHom_comp_innerIso_of_isTransporter` theorem.
That theorem reads the conjugator through the model's actual integral-point
map and its specified generic-fibre identification. Consequently the
construction provides the algebraic conjugator needed to move apartments
while preserving subsets fixed by model integral points. This module itself
does not assert that such a model or initial apartment exists, produce a
special torus containing a prescribed subtorus, or prove the fixed-pair
special-apartment target.

Shared declarations `IsTransporter.comp_innerIso_eq` are imported from `Langlands.GroupScheme.Dynamic.PointedEtaleConjugacy`; their mathematical hypotheses, conclusions and data are unchanged.
