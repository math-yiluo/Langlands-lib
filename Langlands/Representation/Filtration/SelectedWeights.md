# Filtrations of selected generalized weight parts

Author: Worker 1725. Module `Langlands.Representation.Filtration.SelectedWeights`, namespace `Langlands.ObjectRepFiltration`.

This is an internal algebraic construction for the passage to unitary parts in Renard VII.2.5. It restricts an already supplied actual object filtration to any selection of generalized central-map weights and identifies its actual successive quotients. It does not supply a geometric filtration or prove `TemperedGeometricLemmaStatement`.

## Provenance

The source motivation is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.2.5, printed p.230 / PDF p.236. Its proof takes the unitary portions of the geometric-lemma filtration after analyzing the exponents of its pieces. The generalized characteristic spaces are those of VII.1.1, printed p.220 / PDF p.226, and the zero/nonzero real-part partition is that of VII.2.3, printed p.229 / PDF p.235. The registered source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The constructions below generalize the algebraic filtration step to an arbitrary predicate on central-map characters. This generalization and its explicit lifting argument are internal derived content, rather than separate statements attributed verbatim to Renard. They reuse `Langlands.selectedWeightPart`, its intertwiner preservation, its surjective lifting, and its injective membership reflection from `Exponents.SelectedWeights`.

## Actual filtrations and quotients

For a field `R`, a monoid `G`, an actual representation `B : Rep R G`, and a supplied filtration `s : ObjectRepFiltration B n`, `intersect s S` is a filtration of `Rep.of S.toRepresentation` for any actual subrepresentation `S` of `B`. Its `i`th submodule consists literally of those vectors `v : S` whose ambient value lies in `s.subrepresentation i`. The construction pulls each submodule back along the inclusion `S → B`. It inherits monotonicity, begins at zero and ends at all of `S`. The length `n`, index order, repeated steps and zero grades are retained, including when `n = 0`. `mem_intersect_subrepresentation` gives the membership formula, and `intersectStepMap` is the actual inclusion from an intersected step into the corresponding original step.

`gradedEquivOfSurjection s i f hf hker` identifies `s.gradedRepresentation i` with a possibly independently sized target representation. Here `f` is an actual intertwiner from the upper step, `hf` says it is onto, and `hker` says `f v = 0` exactly when the ambient value of `v` lies in the lower step. The implementation descends `f` through the lower-in-upper submodule using `Submodule.liftQ`, proves equivariance on quotient representatives, and proves bijectivity using `hker` and `hf`. It uses the existing actual quotient, not an abstract isomorphic replacement.

## Selecting weights

For the weight constructions, `G` is a group with a topology, a `NonarchimedeanGroup` instance and a `WeaklyLocallyCompactSpace` instance. An arbitrary group `A` maps to its center by `ι : A →* G`, with certificate `hι`; no topology or continuity premise is imposed on `A` or `ι`. The field, acting group, character group and carrier universes are independent. Let `P` be any predicate on characters `A →* Rˣ` and let `S = selectedWeightPart B.ρ ι hι P`.

`selectedFiltration s ι hι P` is exactly `intersect s S`. It is defined without smoothness, admissibility or weight-spanning hypotheses. The graded comparison has the following explicit hypotheses:

- `hB : IsSmooth B.ρ`;
- for the grade `i` being compared, the sum over all `A`-characters of the generalized weight spaces of the original upper-step representation `(s.subrepresentation i.succ).toRepresentation` is the whole upper step.

Under those hypotheses, `selectedUpperProjection` sends an intersected upper-step vector to its image under the original graded projection, regarded as a vector of the selected part of the original quotient. To prove that this image is selected, injective membership reflection along the upper-step inclusion identifies the selected ambient intersection with selected upper-step vectors. Intertwiner preservation then applies to the original quotient projection.

`selectedUpperProjection_surjective` proves that every selected vector of the original quotient has a selected upper-step lift. Smoothness transfers from the ambient representation to the upper step and then to its quotient. Surjectivity of `selectedWeightMap` for the original projection, with upper-step weight spanning, gives a lift. Preservation along the upper-step inclusion places that lift in the literal ambient intersection. No admissibility or spanning hypothesis on the graded quotient is required.

`selectedGradedEquiv s ι hι P hB i hspan` is an actual representation equivalence

`((s.selectedFiltration ι hι P).gradedRepresentation i).ρ ≃ (selectedWeightPart (s.gradedRepresentation i).ρ ι hι P).toRepresentation`.

The equivalence follows from `gradedEquivOfSurjection`: the selected upper projection is onto, and its kernel is precisely the intersected lower step, because its underlying map is the original quotient projection. `selectedGradedEquiv_projection` states that its forward map on an actual quotient representative is this selected upper projection.

Finally, over an algebraically closed field, `selectedGradedEquivOfAdmissible s ι hι P hB i` supplies the same equivalence from `hB : IsAdmissible B.ρ` alone. Admissibility passes through the injective upper-step inclusion; the existing `CentralDecomposition.admissible_centerFinite` and `generalizedWeightSpace_iSup_eq_top` then supply upper-step spanning. This is an implication from explicit ambient admissibility. It does not prove that any geometric-lemma ambient Jacquet representation is admissible.

## Scope

The intended application takes `R = ℂ` and `P χ` to be the zero-normalized-real-part condition for a chosen split component. Applying it to Renard VII.2.5 still requires the actual geometric filtration, the identification of its selected graded pieces with the published `unitaryPieceRep`, the comparison between this generic selection and the published unitary Jacquet module, and any representation-theoretic admissibility or spanning facts used at that application. None of those obligations is asserted by this module.
