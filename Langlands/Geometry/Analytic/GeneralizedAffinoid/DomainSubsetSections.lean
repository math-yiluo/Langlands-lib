import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainOpenSectionsLocalization

/-! # Compatible quotient sections on subsets of a full domain -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory RationalChart

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- Evaluate a compatible family on any contained full domain by actual
restriction followed by canonical recovery of its stored algebra element. -/
def sectionEvaluation {S : Set (BanachSpectrum A)} (U : Domain K A)
    (hU : U.locus ⊆ S) : OpenSections.Sections S →ₐ[K] U.algebra :=
  (fromLocusSections U).comp (OpenSections.restriction hU)

theorem sectionEvaluation_restriction {S T : Set (BanachSpectrum A)}
    (h : S ⊆ T) (U : Domain K A) (hU : U.locus ⊆ S)
    (s : OpenSections.Sections T) :
    sectionEvaluation U hU (OpenSections.restriction h s) =
      sectionEvaluation U (hU.trans h) s := rfl

/-- Evaluation commutes with every actual bounded full-domain restriction. -/
theorem sectionEvaluation_naturality {S : Set (BanachSpectrum A)}
    {U V : Domain K A} (f : U ⟶ V) (hU : U.locus ⊆ S)
    (hV : V.locus ⊆ S) (s : OpenSections.Sections S) :
    f.restriction (sectionEvaluation V hV s) = sectionEvaluation U hU s := by
  change f.restriction (fromLocusSections V (OpenSections.restriction hV s)) = _
  rw [fromLocusSections_restriction]
  rfl

@[simp]
theorem sectionEvaluation_rational {S : Set (BanachSpectrum A)}
    (e : OpenSections.ChartIn S) (s : OpenSections.Sections S) :
    sectionEvaluation e.val.toDomain e.property s = s.val e := by
  change (locusSectionsEquiv e.val.toDomain).symm
    (OpenSections.restriction e.property s) = _
  rw [locusSectionsEquiv_rational]
  rfl

theorem sectionEvaluation_fromBase {S : Set (BanachSpectrum A)}
    (U : Domain K A) (hU : U.locus ⊆ S) (a : A) :
    sectionEvaluation U hU (OpenSections.fromBase S a) = U.baseMap a := by
  change fromLocusSections U (OpenSections.fromBase U.locus a) = _
  rw [← toLocusSections_baseMap, fromLocusSections_toLocusSections]

variable (d : Domain K A)

/-- The image of a full intrinsic domain contained in a preimage is
contained in the original ambient subset. -/
theorem extend_locus_subset_of_preimage {S : Set (BanachSpectrum A)}
    (U : Domain K d.algebra) (hU : U.locus ⊆ d.spectrumMap ⁻¹' S) :
    (d.extend U).locus ⊆ S := by
  rintro _ ⟨x, hx, rfl⟩
  exact hU hx

/-- Pull an ambient compatible quotient family back to an arbitrary subset
of the intrinsic spectrum, evaluating on extended full domains. -/
def toIntrinsicSections (S : Set (BanachSpectrum A)) :
    OpenSections.Sections S →ₐ[K]
      OpenSections.Sections (d.spectrumMap ⁻¹' S) :=
  (AlgHom.pi (fun e : OpenSections.ChartIn (d.spectrumMap ⁻¹' S) =>
    sectionEvaluation (d.extend e.val.toDomain)
      (d.extend_locus_subset_of_preimage e.val.toDomain e.property))).codRestrict
    (OpenSections.compatibleAlgebra _) (by
      intro s e g f
      exact sectionEvaluation_naturality
        (d.extendFunctor.map ((toDomainFunctor K d.algebra).map f)) _ _ s)

@[simp]
theorem toIntrinsicSections_apply (S : Set (BanachSpectrum A))
    (s : OpenSections.Sections S)
    (e : OpenSections.ChartIn (d.spectrumMap ⁻¹' S)) :
    (d.toIntrinsicSections S s).val e =
      sectionEvaluation (d.extend e.val.toDomain)
        (d.extend_locus_subset_of_preimage e.val.toDomain e.property) s := rfl

/-- Any actual ambient inclusion inside `d` gives an intrinsic inclusion
with precisely the same bounded restriction. -/
def relativeMap {U V : Domain K A} (f : U ⟶ V)
    (hU : U.locus ⊆ d.locus) (hV : V.locus ⊆ d.locus) :
    d.relative U (inclusionOfSubset U d hU) ⟶
      d.relative V (inclusionOfSubset V d hV) where
  restriction := f.restriction
  comp_baseMap := congrArg Inclusion.restriction
    (@Subsingleton.elim (Inclusion U d) inferInstance
      (f ≫ inclusionOfSubset V d hV) (inclusionOfSubset U d hU))

@[simp]
theorem relativeMap_restriction {U V : Domain K A} (f : U ⟶ V)
    (hU : U.locus ⊆ d.locus) (hV : V.locus ⊆ d.locus) :
    (d.relativeMap f hU hV).restriction = f.restriction := rfl

/-- Return an intrinsic family on the full preimage of a subset of `d`
to ambient charts by evaluating on their actual relative domains. -/
def fromIntrinsicSections {S : Set (BanachSpectrum A)} (hS : S ⊆ d.locus) :
    OpenSections.Sections (d.spectrumMap ⁻¹' S) →ₐ[K]
      OpenSections.Sections S :=
  (AlgHom.pi (fun e : OpenSections.ChartIn S =>
    sectionEvaluation
      (d.relative e.val.toDomain
        (inclusionOfSubset e.val.toDomain d (e.property.trans hS)))
      ((d.relative_locus_subset_preimage _ _).trans
        (Set.preimage_mono e.property)))).codRestrict
    (OpenSections.compatibleAlgebra _) (by
      intro s e g f
      exact sectionEvaluation_naturality
        (d.relativeMap ((toDomainFunctor K A).map f)
          (e.property.trans hS) (g.property.trans hS)) _ _ s)

@[simp]
theorem fromIntrinsicSections_apply {S : Set (BanachSpectrum A)}
    (hS : S ⊆ d.locus)
    (s : OpenSections.Sections (d.spectrumMap ⁻¹' S))
    (e : OpenSections.ChartIn S) :
    (d.fromIntrinsicSections hS s).val e =
      sectionEvaluation
        (d.relative e.val.toDomain
          (inclusionOfSubset e.val.toDomain d (e.property.trans hS)))
        ((d.relative_locus_subset_preimage _ _).trans
          (Set.preimage_mono e.property)) s := rfl

/-- Evaluation of the pulled-back family on every intrinsic full domain
is the original ambient evaluation on its extension. -/
theorem sectionEvaluation_toIntrinsicSections {S : Set (BanachSpectrum A)}
    (U : Domain K d.algebra) (hU : U.locus ⊆ d.spectrumMap ⁻¹' S)
    (s : OpenSections.Sections S) :
    sectionEvaluation U hU (d.toIntrinsicSections S s) =
      sectionEvaluation (d.extend U)
        (d.extend_locus_subset_of_preimage U hU) s := by
  apply (locusSectionsEquiv U).injective
  change toLocusSections U
      (fromLocusSections U (OpenSections.restriction hU (d.toIntrinsicSections S s))) = _
  rw [toLocusSections_fromLocusSections]
  apply OpenSections.ext
  intro e
  exact (sectionEvaluation_naturality
    (d.extendFunctor.map (inclusionOfSubset e.val.toDomain U e.property))
    _ _ s).symm

/-- Evaluation of the returned family on every ambient full domain is
the intrinsic evaluation on its actual relative representation. -/
theorem sectionEvaluation_fromIntrinsicSections {S : Set (BanachSpectrum A)}
    (hS : S ⊆ d.locus) (U : Domain K A) (hU : U.locus ⊆ S)
    (s : OpenSections.Sections (d.spectrumMap ⁻¹' S)) :
    sectionEvaluation U hU (d.fromIntrinsicSections hS s) =
      sectionEvaluation
        (d.relative U (inclusionOfSubset U d (hU.trans hS)))
        ((d.relative_locus_subset_preimage _ _).trans (Set.preimage_mono hU)) s := by
  apply (locusSectionsEquiv U).injective
  change toLocusSections U
      (fromLocusSections U (OpenSections.restriction hU
        (d.fromIntrinsicSections hS s))) = _
  rw [toLocusSections_fromLocusSections]
  apply OpenSections.ext
  intro e
  exact (sectionEvaluation_naturality
    (d.relativeMap (inclusionOfSubset e.val.toDomain U e.property)
      (e.property.trans (hU.trans hS)) (hU.trans hS)) _ _ s).symm

/-- Returning a pulled-back family preserves every actual ambient chart
element, through the bounded identity on the unchanged relative algebra. -/
@[simp]
theorem fromIntrinsicSections_toIntrinsicSections {S : Set (BanachSpectrum A)}
    (hS : S ⊆ d.locus) (s : OpenSections.Sections S) :
    d.fromIntrinsicSections hS (d.toIntrinsicSections S s) = s := by
  apply OpenSections.ext
  intro e
  change sectionEvaluation
    (d.relative e.val.toDomain
      (inclusionOfSubset e.val.toDomain d (e.property.trans hS))) _
    (d.toIntrinsicSections S s) = _
  rw [sectionEvaluation_toIntrinsicSections]
  let f : d.extend (d.relative e.val.toDomain
      (inclusionOfSubset e.val.toDomain d (e.property.trans hS))) ⟶
      e.val.toDomain :=
    ⟨BoundedAlgHom.id K e.val.algebra,
      (inclusionOfSubset e.val.toDomain d (e.property.trans hS)).comp_baseMap.symm⟩
  exact (sectionEvaluation_naturality f _ e.property s).symm.trans
    (sectionEvaluation_rational e s)

/-- Pulling back a returned family preserves every actual intrinsic chart
element, since its relative extension retains the same algebra. -/
@[simp]
theorem toIntrinsicSections_fromIntrinsicSections {S : Set (BanachSpectrum A)}
    (hS : S ⊆ d.locus)
    (s : OpenSections.Sections (d.spectrumMap ⁻¹' S)) :
    d.toIntrinsicSections S (d.fromIntrinsicSections hS s) = s := by
  apply OpenSections.ext
  intro e
  change sectionEvaluation (d.extend e.val.toDomain) _
    (d.fromIntrinsicSections hS s) = _
  rw [sectionEvaluation_fromIntrinsicSections]
  let hE : (d.extend e.val.toDomain).locus ⊆ d.locus :=
    (d.extend_locus_subset_of_preimage e.val.toDomain e.property).trans hS
  let f : e.val.toDomain ⟶
      d.relative (d.extend e.val.toDomain)
        (inclusionOfSubset (d.extend e.val.toDomain) d hE) := {
    restriction := BoundedAlgHom.id K e.val.algebra
    comp_baseMap := congrArg Inclusion.restriction
      (@Subsingleton.elim (Inclusion (d.extend e.val.toDomain) d) inferInstance
        (inclusionOfSubset (d.extend e.val.toDomain) d hE)
        (d.extendInclusion e.val.toDomain)) }
  exact (sectionEvaluation_naturality f e.property _ s).trans
    (sectionEvaluation_rational e s)

/-- Intrinsic and ambient compatible quotient sections agree on every
subset contained in a full domain, with no openness assumption. -/
def subsetSectionsEquiv {S : Set (BanachSpectrum A)} (hS : S ⊆ d.locus) :
    OpenSections.Sections S ≃ₐ[K]
      OpenSections.Sections (d.spectrumMap ⁻¹' S) :=
  AlgEquiv.ofAlgHom (d.toIntrinsicSections S) (d.fromIntrinsicSections hS)
    (by
      apply AlgHom.ext
      intro s
      exact d.toIntrinsicSections_fromIntrinsicSections hS s)
    (by
      apply AlgHom.ext
      intro s
      exact d.fromIntrinsicSections_toIntrinsicSections hS s)

@[simp]
theorem subsetSectionsEquiv_apply {S : Set (BanachSpectrum A)}
    (hS : S ⊆ d.locus) (s : OpenSections.Sections S) :
    d.subsetSectionsEquiv hS s = d.toIntrinsicSections S s := rfl

@[simp]
theorem subsetSectionsEquiv_symm_apply {S : Set (BanachSpectrum A)}
    (hS : S ⊆ d.locus)
    (s : OpenSections.Sections (d.spectrumMap ⁻¹' S)) :
    (d.subsetSectionsEquiv hS).symm s = d.fromIntrinsicSections hS s := rfl

/-- The forward maps commute with every inclusion of ambient subsets. -/
theorem toIntrinsicSections_restriction {S T : Set (BanachSpectrum A)}
    (h : S ⊆ T) (s : OpenSections.Sections T) :
    d.toIntrinsicSections S (OpenSections.restriction h s) =
      OpenSections.restriction (Set.preimage_mono h) (d.toIntrinsicSections T s) := rfl

/-- The inverse maps commute with every inclusion of subsets of the
represented locus. -/
theorem fromIntrinsicSections_restriction {S T : Set (BanachSpectrum A)}
    (h : S ⊆ T) (hT : T ⊆ d.locus)
    (s : OpenSections.Sections (d.spectrumMap ⁻¹' T)) :
    d.fromIntrinsicSections (h.trans hT)
        (OpenSections.restriction (Set.preimage_mono h) s) =
      OpenSections.restriction h (d.fromIntrinsicSections hT s) := rfl

/-- The forward comparison keeps the original composite structural maps. -/
@[simp]
theorem toIntrinsicSections_fromBase (S : Set (BanachSpectrum A)) (a : A) :
    d.toIntrinsicSections S (OpenSections.fromBase S a) =
      OpenSections.fromBase (d.spectrumMap ⁻¹' S) (d.baseMap a) := by
  apply OpenSections.ext
  intro e
  exact sectionEvaluation_fromBase (d.extend e.val.toDomain) _ a

/-- Intrinsic base elements return to their actual ambient restriction
families from the containing domain. -/
theorem fromIntrinsicSections_fromBase {S : Set (BanachSpectrum A)}
    (hS : S ⊆ d.locus) (a : d.algebra) :
    d.fromIntrinsicSections hS
        (OpenSections.fromBase (d.spectrumMap ⁻¹' S) a) =
      OpenSections.restriction hS (toLocusSections d a) := by
  apply OpenSections.ext
  intro e
  exact sectionEvaluation_fromBase
    (d.relative e.val.toDomain
      (inclusionOfSubset e.val.toDomain d (e.property.trans hS))) _ a

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
