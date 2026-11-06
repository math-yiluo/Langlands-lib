import Langlands.Geometry.Analytic.FullRecognitionIdempotence

/-! # Full bounded naturality of recognition idempotence -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- The canonical original-chart map commutes with restriction between
outer recognized parents as an entire bounded algebra homomorphism. -/
theorem recognitionChartDomain_comp_restriction
    (U V : a.recognitionAtlas.saturatedAtlas.RecognizedSubset)
    (hUV : U.locus ⊆ V.locus) (s : a.Index)
    (hs : Set.range (a.chart s) ⊆ U.locus) :
    (a.recognitionChartDomain U s hs).baseMap.comp (U.restriction V hUV) =
      (a.recognitionChartDomain V s (hs.trans hUV)).baseMap := by
  let S := a.recognitionOriginalSaturatedIndex s
  let p : BoundedAlgHom K (a.recognitionAtlas.saturatedAtlas.algebra S) (a.algebra s) :=
    (a.recognitionOriginalDomain s).baseMap.comp
      (a.recognitionOriginalToSaturated s).restriction
  have h := U.originalRestriction_comp_restriction V hUV
    S
    ((a.recognitionOriginalSaturatedIndex_range s).subset.trans hs)
  have hU := congrArg
    (fun q : BoundedAlgHom K U.algebra (a.algebra s) =>
      q.comp (U.restriction V hUV))
    (a.recognitionChartDomain_baseMap U s hs)
  have hA :
      (p.comp (U.originalRestriction S
        ((a.recognitionOriginalSaturatedIndex_range s).subset.trans hs))).comp
          (U.restriction V hUV) =
      p.comp ((U.originalRestriction S
        ((a.recognitionOriginalSaturatedIndex_range s).subset.trans hs)).comp
          (U.restriction V hUV)) := rfl
  have hP := congrArg
    (fun q : BoundedAlgHom K V.algebra
      (a.recognitionAtlas.saturatedAtlas.algebra S) => p.comp q) h
  exact hU.trans
    (hA.trans (hP.trans (a.recognitionChartDomain_baseMap V s (hs.trans hUV)).symm))

namespace RecognizedSubset

variable {a} (V : a.RecognizedSubset)

/-- Any actual realization comparison recovers all original restrictions
through the finite section equalizers, not only the defining components. -/
theorem originalRestriction_comp_affinoidRealization
    (d : FiniteChartGluingData a) [T2Space d.locus]
    (hd : d.locus = V.locus) (c : d.AffinoidRealization)
    (s : a.Index) (hs : Set.range (a.chart s) ⊆ V.locus) :
    (V.originalRestriction s hs).comp
        ((V.val.realizationSectionEquiv d hd c).trans
          V.property.algebraEquiv.symm).toBoundedAlgHom =
      (d.originalRestriction s (hs.trans hd.symm.subset)).comp
        c.restrictFromParent := by
  have h := d.originalRestriction_comp_restrictionTo V.val.gluingData
    (V.val.gluingData_locus.trans hd.symm).subset s
    (hs.trans V.val.gluingData_locus.symm.subset)
  ext x
  change V.val.gluingData.originalRestriction s _
      (V.property.algebraEquiv
        (V.property.algebraEquiv.symm
          ((V.val.comparisonEquiv d hd).symm (c.sectionAlgEquiv x)))) = _
  rw [V.property.algebraEquiv.apply_symm_apply]
  exact congrArg
    (fun q : BoundedAlgHom K d.SectionAlgebra (a.algebra s) =>
      q (c.sectionAlgEquiv x)) h

end RecognizedSubset

variable (W : a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset)

/-- The realized section restriction to every contained original chart
equals its canonical nested original-chart map on all algebra elements. -/
theorem iteratedRecognition_originalRestriction
    (s : a.saturatedAtlas.Index)
    (hs : Set.range (a.saturatedAtlas.chart s) ⊆ W.locus) :
    let d := a.iteratedRecognitionGluing W
    let c := a.iteratedRecognitionAffinoidRealization W
    letI : T2Space d.locus := c.locusHomeomorph.symm.t2Space
    (d.originalRestriction s
      (hs.trans (a.iteratedRecognitionGluing_locus W).symm.subset)).comp
        c.restrictFromParent =
      (a.saturatedAtlas.recognitionChartDomain W s hs).baseMap := by
  let d := a.iteratedRecognitionGluing W
  let c := a.iteratedRecognitionAffinoidRealization W
  let : T2Space d.locus := c.locusHomeomorph.symm.t2Space
  let hs' := hs.trans (a.iteratedRecognitionGluing_locus W).symm.subset
  let C := d.subordinateCoverOfHausdorff s hs'
  ext x
  apply C.domainCover.algebra_ext_of_restrict_eq
  intro t
  have hd := d.original_comp_originalRestriction s hs' (C.index t)
    (C.subset_parent t) (C.member t) (C.subset_member t)
  have hp := a.saturatedAtlas.recognitionChartDomain_naturality W (C.index t) s
    ((C.subset_parent t).trans hs) hs (C.subset_parent t)
  have hm := a.saturatedAtlas.recognitionChartDomain_naturality W
    (C.index t) (d.index (C.member t)) ((C.subset_parent t).trans hs)
    (a.iteratedRecognitionChartIndex_subset W (C.member t)) (C.subset_member t)
  exact (congrArg
    (fun q : BoundedAlgHom K d.SectionAlgebra (a.saturatedAtlas.algebra (C.index t)) =>
      q (c.restrictFromParent x)) hd).trans
        ((congrArg
          (fun q : BoundedAlgHom K W.algebra (a.saturatedAtlas.algebra (C.index t)) =>
            q x) hm).trans
              (congrArg
                (fun q : BoundedAlgHom K W.algebra
                  (a.saturatedAtlas.algebra (C.index t)) => q x) hp).symm)

/-- The constructed idempotence equivalence recovers the complete bounded
restriction to every contained original first-saturation chart. -/
theorem fullRecognitionIdempotenceAlgebraEquiv_originalRestriction
    (s : a.saturatedAtlas.Index)
    (hs : Set.range (a.saturatedAtlas.chart s) ⊆ W.locus) :
    ((a.fullRecognitionIdempotenceIndex W).originalRestriction s hs).comp
        (a.fullRecognitionIdempotenceAlgebraEquiv W).toBoundedAlgHom =
      (a.saturatedAtlas.recognitionChartDomain W s hs).baseMap := by
  let d := a.iteratedRecognitionGluing W
  let c := a.iteratedRecognitionAffinoidRealization W
  let : T2Space d.locus := c.locusHomeomorph.symm.t2Space
  exact ((a.fullRecognitionIdempotenceIndex W).originalRestriction_comp_affinoidRealization
    d (a.iteratedRecognitionGluing_locus W) c s hs).trans
      (a.iteratedRecognition_originalRestriction W s hs)

/-- The pointwise bounded algebra comparisons are natural for every
nested pair of iterated recognized charts, on their entire algebras. -/
theorem fullRecognitionIdempotenceAlgebraEquiv_naturality
    (U V : a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset)
    (hUV : U.locus ⊆ V.locus) :
    (a.fullRecognitionIdempotenceAlgebraEquiv U).toBoundedAlgHom.comp
        (U.restriction V hUV) =
      ((a.fullRecognitionIdempotenceIndex U).restriction
        (a.fullRecognitionIdempotenceIndex V) hUV).comp
          (a.fullRecognitionIdempotenceAlgebraEquiv V).toBoundedAlgHom := by
  let Y : a.saturatedAtlas.RecognizedSubset := a.fullRecognitionIdempotenceIndex U
  let Z : a.saturatedAtlas.RecognizedSubset := a.fullRecognitionIdempotenceIndex V
  ext x
  apply Y.componentCover.algebra_ext_of_restrict_eq
  intro i
  change (Y.property.componentDomain i).baseMap
      ((a.fullRecognitionIdempotenceAlgebraEquiv U) (U.restriction V hUV x)) =
    (Y.property.componentDomain i).baseMap
      (Y.restriction Z hUV ((a.fullRecognitionIdempotenceAlgebraEquiv V) x))
  have hD := Y.componentDomain_baseMap i
  apply (congrArg
    (fun q : BoundedAlgHom K Y.algebra
      (a.saturatedAtlas.algebra (Y.property.cover.index i)) =>
        q ((a.fullRecognitionIdempotenceAlgebraEquiv U) (U.restriction V hUV x)))
    hD).trans
  apply Eq.trans _ (congrArg
    (fun q : BoundedAlgHom K Y.algebra
      (a.saturatedAtlas.algebra (Y.property.cover.index i)) =>
        q (Y.restriction Z hUV ((a.fullRecognitionIdempotenceAlgebraEquiv V) x)))
    hD).symm
  have hU := a.fullRecognitionIdempotenceAlgebraEquiv_originalRestriction U
    (Y.property.cover.index i) (Y.component_subset i)
  have hV := a.fullRecognitionIdempotenceAlgebraEquiv_originalRestriction V
    (Y.property.cover.index i) ((Y.component_subset i).trans hUV)
  have hO := a.saturatedAtlas.recognitionChartDomain_comp_restriction U V hUV
    (Y.property.cover.index i) (Y.component_subset i)
  have hY := Y.originalRestriction_comp_restriction Z hUV
    (Y.property.cover.index i) (Y.component_subset i)
  exact (congrArg
    (fun q : BoundedAlgHom K U.algebra (a.saturatedAtlas.algebra (Y.property.cover.index i)) =>
      q (U.restriction V hUV x)) hU).trans
        ((congrArg
          (fun q : BoundedAlgHom K V.algebra
            (a.saturatedAtlas.algebra (Y.property.cover.index i)) => q x) hO).trans
          ((congrArg
            (fun q : BoundedAlgHom K V.algebra
              (a.saturatedAtlas.algebra (Y.property.cover.index i)) => q x) hV).symm.trans
            (congrArg
              (fun q : BoundedAlgHom K Z.algebra
                (a.saturatedAtlas.algebra (Y.property.cover.index i)) =>
                  q ((a.fullRecognitionIdempotenceAlgebraEquiv V) x)) hY).symm))

/-- The constructed old recognized presentation defines an actual
functor on all literal inclusions of iterated recognized charts. -/
def fullRecognitionIdempotenceFunctor :
    a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset ⥤
      a.saturatedAtlas.RecognizedSubset where
  obj := a.fullRecognitionIdempotenceIndex
  map f := ⟨f.subset⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem fullRecognitionIdempotenceFunctor_locus
    (U : a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset) :
    (a.fullRecognitionIdempotenceFunctor.obj U).locus = U.locus := rfl

/-- The functor's actual bounded restrictions are intertwined by the
constructed comparison equivalences on every algebra element. -/
theorem fullRecognitionIdempotenceFunctor_naturality
    {U V : a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset} (f : U ⟶ V) :
    (a.fullRecognitionIdempotenceAlgebraEquiv U).toBoundedAlgHom.comp f.restriction =
      (a.fullRecognitionIdempotenceFunctor.map f).restriction.comp
        (a.fullRecognitionIdempotenceAlgebraEquiv V).toBoundedAlgHom :=
  a.fullRecognitionIdempotenceAlgebraEquiv_naturality U V f.subset

end Langlands.Analytic.IndexedAffinoidAtlas
