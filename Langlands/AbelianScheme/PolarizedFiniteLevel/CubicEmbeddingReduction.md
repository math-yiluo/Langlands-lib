# The relative cubic embedding from its field case

This internal module derives the relative cubic projective embedding of an
ordinary polarized datum from its field case. The field case is the statement
`CubicFieldEmbeddingStatement` in the separate module of that name. This
module takes it as an explicit hypothesis `HF` and does not prove it. All
schemes lie in one arbitrary universe `u`.

Fix `P : Prerequisites`, a locally noetherian scheme `S`, natural numbers
`g d n` with `0 < d`, and a datum `a : Datum P S g d n` with abelian
structure map `π = a.abelian.X.hom`.

## Results

**Generation.** `Datum.cubicEvaluationGenerates_of_fieldEmbedding` proves
`EvaluationGenerates π a.cubicBundle (𝟙 a.rigidificationModule)`. It applies
the published `Datum.cubicEvaluationGenerates_of_directImage` with the
published theorem `cubicDirectImage`. The fibre hypothesis there is
epimorphy of the cubic counit of `a.pullback (S.fromSpecResidueField s)`.
This is the first clause of `HF` for the field `S.residueField s`.

**Closed immersion.** `Datum.isClosedImmersion_cubicProjectiveEvaluation_of_fieldEmbedding`:
for every rank witness
`hM : IsLocallyFreeOfRank a.rigidificationModule (6 ^ g * d)` and every
generation witness `hgen`, the published `Datum.cubicProjectiveEvaluation hd hM hgen`
is a closed immersion. This morphism goes from the abelian scheme to the
projective bundle of the cubic direct image.

The proof reuses the published Library lemmas for the actual residue fibres
of this evaluation:

1. By the published `Datum.isClosedImmersion_cubicProjectiveEvaluation_iff_fibre`
   (module `CubicProjectiveFibres`), it suffices to show that the actual
   fibre evaluation `Datum.cubicProjectiveEvaluationFibre hd hM hgen s` is a
   closed immersion for every `s : S`.
2. Fix `s`. Choose an affine frame open `U` containing `s` with the published
   `exists_affine_frameOpen`. The published `cubicDirectImage` makes the
   canonical base-change map `a.rigidificationBaseChangeMap` along
   `S.fromSpecResidueField s` an isomorphism. This is the hypothesis of the
   published fibre-section basis.
3. The published `Datum.cubicFibreSectionBasis U hU s hs` (module
   `CubicFibreSections`) is a basis of all global sections of the cubic
   bundle of the residue datum `a.pullback (S.fromSpecResidueField s)`. The
   published `Datum.cubicFibreSectionBasis_generate` shows that its entries
   generate. The second clause of `HF`, for this basis, makes its relative
   linear-system map over `Spec (S.residueField s)` a closed immersion.
4. The published `Datum.cubicFibreSectionBasis_coordinates` identifies this
   map with the published `fibreEvaluationCoordinates` in the frame `U`.
   Composing with the isomorphism `FrameBundle.fibreChartIso` keeps it a
   closed immersion. The published `fibreEvaluationCoordinates_fibreChartIso`
   identifies the composite with the map of residue fibres induced by the
   evaluation. That map is by definition `Datum.cubicProjectiveEvaluationFibre`.

**Packaged result.** `Datum.cubicProjectiveEmbedding_of_fieldEmbedding` is a
proved definition (a `def` whose type is a proposition) and is the declaration
named by the submission. Assuming `HF`, it states that the following exist:
- the rank witness `IsLocallyFreeOfRank a.rigidificationModule (6 ^ g * d)`,
  supplied by `cubicDirectImage`;
- a generation witness;

and that, for these witnesses, the actual cubic projective evaluation is a
closed immersion.

## Provenance

This is an internal derivation. It adds no new external mathematical claim
and introduces no new construction. It combines the published Library
modules `CubicEvaluation`, `CubicProjectiveEvaluation`, `CubicProjectiveFibres`,
`CubicFibreSections`, `CubicDirectImageProof` and
`ProjectiveBundle/EvaluationFibreCoordinates`. The mathematical step it
carries out is the one in Mumford, Fogarty and Kirwan, *Geometric Invariant
Theory*, third edition (1994), Chapter 7 §2, printed pp. 130-131. There the
abelian scheme is embedded in the projective bundle of the rank `6^g d`
direct image of the cubic bundle over the base.

The Lefschetz field statement itself remains an explicit hypothesis. No moduli
representability, Hilbert scheme or quotient statement is asserted here.
