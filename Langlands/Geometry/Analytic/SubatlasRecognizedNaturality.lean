import Langlands.Geometry.Analytic.SubatlasRecognizedRecognition
import Langlands.Geometry.Analytic.FullRecognitionNaturality
import Langlands.Geometry.Analytic.RecognizedLocalDomainCategory

/-! # Full bounded naturality of selected recognition of recognized subsets -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  {P : a.Index → Prop} (hP : a.IsLocallyRefiningSelection P)

/-- Canonical selected-chart full domains commute with every original
recognized inclusion as entire bounded algebra homomorphisms. -/
theorem subatlasRecognizedChartDomain_comp_restriction
    (U V : a.saturatedAtlas.RecognizedSubset) (hUV : U.locus ⊆ V.locus)
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ U.locus) :
    (a.subatlasRecognizedChartDomain hP U s hs).baseMap.comp (U.restriction V hUV) =
      (a.subatlasRecognizedChartDomain hP V s (hs.trans hUV)).baseMap := by
  let S := a.subatlasSaturatedOriginalIndex P hP s
  let p := (a.subatlasSaturatedToOriginal P hP s).restriction
  have h := U.originalRestriction_comp_restriction V hUV S
    ((a.subatlasSaturatedOriginalIndex_range P hP s).subset.trans hs)
  have hU := congrArg
    (fun q : BoundedAlgHom K U.algebra ((a.subatlas P hP).saturatedAtlas.algebra s) =>
      q.comp (U.restriction V hUV))
    (a.subatlasRecognizedChartDomain_baseMap hP U s hs)
  have hA :
      (p.comp (U.originalRestriction S
        ((a.subatlasSaturatedOriginalIndex_range P hP s).subset.trans hs))).comp
          (U.restriction V hUV) =
      p.comp ((U.originalRestriction S
        ((a.subatlasSaturatedOriginalIndex_range P hP s).subset.trans hs)).comp
          (U.restriction V hUV)) := rfl
  have hP' := congrArg
    (fun q : BoundedAlgHom K V.algebra (a.saturatedAtlas.algebra S) => p.comp q) h
  exact hU.trans
    (hA.trans (hP'.trans (a.subatlasRecognizedChartDomain_baseMap hP V s (hs.trans hUV)).symm))

variable (W : a.saturatedAtlas.RecognizedSubset)

/-- The realized section restriction to every contained selected saturated chart
equals its canonical full-domain map on all algebra elements. -/
theorem subatlasRecognition_originalRestriction
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ W.locus) :
    let d := a.subatlasRecognitionGluing hP W
    let c := a.subatlasRecognitionAffinoidRealization hP W
    letI : T2Space d.locus := c.locusHomeomorph.symm.t2Space
    (d.originalRestriction s
      (hs.trans (a.subatlasRecognitionGluing_locus hP W).symm.subset)).comp
        c.restrictFromParent =
      (a.subatlasRecognizedChartDomain hP W s hs).baseMap := by
  let d := a.subatlasRecognitionGluing hP W
  let c := a.subatlasRecognitionAffinoidRealization hP W
  let : T2Space d.locus := c.locusHomeomorph.symm.t2Space
  let hs' := hs.trans (a.subatlasRecognitionGluing_locus hP W).symm.subset
  let C := d.subordinateCoverOfHausdorff s hs'
  ext x
  apply C.domainCover.algebra_ext_of_restrict_eq
  intro t
  have hd := d.original_comp_originalRestriction s hs' (C.index t)
    (C.subset_parent t) (C.member t) (C.subset_member t)
  have hp := a.subatlasRecognizedChartDomain_naturality hP W (C.index t) s
    ((C.subset_parent t).trans hs) hs (C.subset_parent t)
  have hm := a.subatlasRecognizedChartDomain_naturality hP W
    (C.index t) (d.index (C.member t)) ((C.subset_parent t).trans hs)
    (a.subatlasRecognitionChartIndex_subset hP W (C.member t)) (C.subset_member t)
  exact (congrArg
    (fun q : BoundedAlgHom K d.SectionAlgebra ((a.subatlas P hP).saturatedAtlas.algebra (C.index t)) =>
      q (c.restrictFromParent x)) hd).trans
        ((congrArg
          (fun q : BoundedAlgHom K W.algebra ((a.subatlas P hP).saturatedAtlas.algebra (C.index t)) =>
            q x) hm).trans
              (congrArg
                (fun q : BoundedAlgHom K W.algebra
                  ((a.subatlas P hP).saturatedAtlas.algebra (C.index t)) => q x) hp).symm)

/-- The constructed selected recognition equivalence recovers the complete
bounded restriction to every contained selected saturated chart. -/
theorem subatlasRecognizedSubsetEquiv_originalRestriction
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ W.locus) :
    ((a.subatlasRecognizedSubset hP W).originalRestriction s hs).comp
        (a.subatlasRecognizedSubsetEquiv hP W).toBoundedAlgHom =
      (a.subatlasRecognizedChartDomain hP W s hs).baseMap := by
  let d := a.subatlasRecognitionGluing hP W
  let c := a.subatlasRecognitionAffinoidRealization hP W
  let : T2Space d.locus := c.locusHomeomorph.symm.t2Space
  exact ((a.subatlasRecognizedSubset hP W).originalRestriction_comp_affinoidRealization
    d (a.subatlasRecognitionGluing_locus hP W) c s hs).trans
      (a.subatlasRecognition_originalRestriction hP W s hs)

/-- The pointwise bounded algebra comparisons are natural for every
nested pair of original recognized subsets, on their entire algebras. -/
theorem subatlasRecognizedSubsetEquiv_naturality
    (U V : a.saturatedAtlas.RecognizedSubset)
    (hUV : U.locus ⊆ V.locus) :
    (a.subatlasRecognizedSubsetEquiv hP U).toBoundedAlgHom.comp
        (U.restriction V hUV) =
      ((a.subatlasRecognizedSubset hP U).restriction
        (a.subatlasRecognizedSubset hP V) hUV).comp
          (a.subatlasRecognizedSubsetEquiv hP V).toBoundedAlgHom := by
  let Y : (a.subatlas P hP).saturatedAtlas.RecognizedSubset := a.subatlasRecognizedSubset hP U
  let Z : (a.subatlas P hP).saturatedAtlas.RecognizedSubset := a.subatlasRecognizedSubset hP V
  ext x
  apply Y.componentCover.algebra_ext_of_restrict_eq
  intro i
  change (Y.property.componentDomain i).baseMap
      ((a.subatlasRecognizedSubsetEquiv hP U) (U.restriction V hUV x)) =
    (Y.property.componentDomain i).baseMap
      (Y.restriction Z hUV ((a.subatlasRecognizedSubsetEquiv hP V) x))
  have hD := Y.componentDomain_baseMap i
  apply (congrArg
    (fun q : BoundedAlgHom K Y.algebra
      ((a.subatlas P hP).saturatedAtlas.algebra (Y.property.cover.index i)) =>
        q ((a.subatlasRecognizedSubsetEquiv hP U) (U.restriction V hUV x)))
    hD).trans
  apply Eq.trans _ (congrArg
    (fun q : BoundedAlgHom K Y.algebra
      ((a.subatlas P hP).saturatedAtlas.algebra (Y.property.cover.index i)) =>
        q (Y.restriction Z hUV ((a.subatlasRecognizedSubsetEquiv hP V) x)))
    hD).symm
  have hU := a.subatlasRecognizedSubsetEquiv_originalRestriction hP U
    (Y.property.cover.index i) (Y.component_subset i)
  have hV := a.subatlasRecognizedSubsetEquiv_originalRestriction hP V
    (Y.property.cover.index i) ((Y.component_subset i).trans hUV)
  have hO := a.subatlasRecognizedChartDomain_comp_restriction hP U V hUV
    (Y.property.cover.index i) (Y.component_subset i)
  have hY := Y.originalRestriction_comp_restriction Z hUV
    (Y.property.cover.index i) (Y.component_subset i)
  exact (congrArg
    (fun q : BoundedAlgHom K U.algebra ((a.subatlas P hP).saturatedAtlas.algebra (Y.property.cover.index i)) =>
      q (U.restriction V hUV x)) hU).trans
        ((congrArg
          (fun q : BoundedAlgHom K V.algebra
            ((a.subatlas P hP).saturatedAtlas.algebra (Y.property.cover.index i)) => q x) hO).trans
          ((congrArg
            (fun q : BoundedAlgHom K V.algebra
              ((a.subatlas P hP).saturatedAtlas.algebra (Y.property.cover.index i)) => q x) hV).symm.trans
            (congrArg
              (fun q : BoundedAlgHom K Z.algebra
                ((a.subatlas P hP).saturatedAtlas.algebra (Y.property.cover.index i)) =>
                  q ((a.subatlasRecognizedSubsetEquiv hP V) x)) hY).symm))

/-- The constructed selected recognized presentation defines an actual
functor on all literal inclusions of original recognized subsets. -/
def subatlasRecognitionFunctor :
    a.saturatedAtlas.RecognizedSubset ⥤
      (a.subatlas P hP).saturatedAtlas.RecognizedSubset where
  obj := a.subatlasRecognizedSubset hP
  map f := ⟨f.subset⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem subatlasRecognitionFunctor_locus
    (U : a.saturatedAtlas.RecognizedSubset) :
    ((a.subatlasRecognitionFunctor hP).obj U).locus = U.locus := rfl

/-- The functor's actual bounded restrictions are intertwined by the
constructed comparison equivalences on every algebra element. -/
theorem subatlasRecognitionFunctor_naturality
    {U V : a.saturatedAtlas.RecognizedSubset} (f : U ⟶ V) :
    (a.subatlasRecognizedSubsetEquiv hP U).toBoundedAlgHom.comp f.restriction =
      ((a.subatlasRecognitionFunctor hP).map f).restriction.comp
        (a.subatlasRecognizedSubsetEquiv hP V).toBoundedAlgHom :=
  a.subatlasRecognizedSubsetEquiv_naturality hP U V f.subset

/-- Actual mutually inverse bounded maps compare the selected and original
recognized algebra presentations. -/
def subatlasRecognitionAffinoidIso (V : a.saturatedAtlas.RecognizedSubset) :
    Opposite.op (a.subatlasRecognizedSubset hP V).algebra ≅ Opposite.op V.algebra where
  hom := Quiver.Hom.op
    (show V.algebra ⟶ (a.subatlasRecognizedSubset hP V).algebra from
      (a.subatlasRecognizedSubsetEquiv hP V).toBoundedAlgHom)
  inv := Quiver.Hom.op
    (show (a.subatlasRecognizedSubset hP V).algebra ⟶ V.algebra from
      (a.subatlasRecognizedSubsetEquiv hP V).symm.toBoundedAlgHom)
  hom_inv_id := congrArg
    (fun q : (a.subatlasRecognizedSubset hP V).algebra ⟶
      (a.subatlasRecognizedSubset hP V).algebra => Quiver.Hom.op q)
    (BoundedAlgHom.ext fun x => (a.subatlasRecognizedSubsetEquiv hP V).apply_symm_apply x)
  inv_hom_id := congrArg (fun q : V.algebra ⟶ V.algebra => Quiver.Hom.op q)
    (BoundedAlgHom.ext fun x => (a.subatlasRecognizedSubsetEquiv hP V).symm_apply_apply x)

/-- The selected recognition functor identifies entire affinoid diagrams
through the proved full bounded naturality equations. -/
def subatlasRecognitionAffinoidNatIso :
    a.subatlasRecognitionFunctor hP ⋙
        RecognizedSubset.toAffinoidSpace (a.subatlas P hP).saturatedAtlas ≅
      RecognizedSubset.toAffinoidSpace a.saturatedAtlas :=
  NatIso.ofComponents (a.subatlasRecognitionAffinoidIso hP) (by
    intro U V f
    exact congrArg
      (fun q : V.algebra ⟶ (a.subatlasRecognizedSubset hP U).algebra =>
        Quiver.Hom.op q)
      (a.subatlasRecognitionFunctor_naturality hP f).symm)

/-- The natural comparison intertwines the actual spectrum maps over the
unchanged ambient space. -/
theorem subatlasRecognitionAffinoidNatIso_over_ambient
    (V : a.saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum (a.subatlasRecognizedSubset hP V).algebra) :
    V.chart ((affinoidSpectrumFunctor K).map
        ((a.subatlasRecognitionAffinoidNatIso hP).hom.app V) x) =
      (a.subatlasRecognizedSubset hP V).chart x :=
  (a.subatlasRecognizedSubset_chart hP V x).symm

end Langlands.Analytic.IndexedAffinoidAtlas
