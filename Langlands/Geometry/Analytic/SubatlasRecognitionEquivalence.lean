import Langlands.Geometry.Analytic.SubatlasRecognizedNaturality
import Langlands.Geometry.Analytic.SubatlasReverseRecognition

/-! # Subatlas invariance of recognized categories and actual affinoid diagrams -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  {P : a.Index → Prop} (hP : a.IsLocallyRefiningSelection P)

/-- Reverse recognition acts on every actual recognized inclusion through
the proved equality of its literal ambient locus. -/
def subatlasReverseRecognitionFunctor :
    (a.subatlas P hP).saturatedAtlas.RecognizedSubset ⥤
      a.saturatedAtlas.RecognizedSubset where
  obj := a.subatlasReverseRecognizedSubset hP
  map {U V} f := ⟨by
    rw [a.subatlasReverseRecognizedSubset_locus, a.subatlasReverseRecognizedSubset_locus]
    exact f.subset⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem subatlasReverseRecognitionFunctor_locus
    (V : (a.subatlas P hP).saturatedAtlas.RecognizedSubset) :
    ((a.subatlasReverseRecognitionFunctor hP).obj V).locus = V.locus :=
  a.subatlasReverseRecognizedSubset_locus hP V

/-- The original round trip is an actual recognized isomorphism through
the unchanged literal subset. Its algebra maps are canonical restrictions. -/
def subatlasRecognitionUnitComponent (V : a.saturatedAtlas.RecognizedSubset) :
    V ≅ (a.subatlasReverseRecognitionFunctor hP).obj
      ((a.subatlasRecognitionFunctor hP).obj V) where
  hom := ⟨(a.subatlasReverseRecognizedSubset_locus hP
    (a.subatlasRecognizedSubset hP V)).symm.subset⟩
  inv := ⟨(a.subatlasReverseRecognizedSubset_locus hP
    (a.subatlasRecognizedSubset hP V)).subset⟩
  hom_inv_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _

def subatlasRecognitionUnitIso :
    𝟭 a.saturatedAtlas.RecognizedSubset ≅
      a.subatlasRecognitionFunctor hP ⋙ a.subatlasReverseRecognitionFunctor hP :=
  NatIso.ofComponents (a.subatlasRecognitionUnitComponent hP) (by
    intro U V f
    exact @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _)

/-- The selected round trip gives actual recognized inclusions both ways,
with bounded mutually inverse restriction maps. -/
def subatlasRecognitionCounitComponent
    (V : (a.subatlas P hP).saturatedAtlas.RecognizedSubset) :
    (a.subatlasRecognitionFunctor hP).obj
      ((a.subatlasReverseRecognitionFunctor hP).obj V) ≅ V where
  hom := ⟨(a.subatlasReverseRecognizedSubset_locus hP V).subset⟩
  inv := ⟨(a.subatlasReverseRecognizedSubset_locus hP V).symm.subset⟩
  hom_inv_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _

def subatlasRecognitionCounitIso :
    a.subatlasReverseRecognitionFunctor hP ⋙ a.subatlasRecognitionFunctor hP ≅
      𝟭 (a.subatlas P hP).saturatedAtlas.RecognizedSubset :=
  NatIso.ofComponents (a.subatlasRecognitionCounitComponent hP) (by
    intro U V f
    exact @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _)

/-- Locally refining selection preserves the entire recognized inclusion
category, using the independently constructed recognition functors. -/
def subatlasRecognitionEquivalence :
    a.saturatedAtlas.RecognizedSubset ≌
      (a.subatlas P hP).saturatedAtlas.RecognizedSubset where
  functor := a.subatlasRecognitionFunctor hP
  inverse := a.subatlasReverseRecognitionFunctor hP
  unitIso := a.subatlasRecognitionUnitIso hP
  counitIso := a.subatlasRecognitionCounitIso hP
  functor_unitIso_comp _ := @Subsingleton.elim
    (RecognizedSubset.Inclusion _ _) inferInstance _ _

/-- In particular, selection preserves the literal family of all
recognized affinoid subsets, in both directions. -/
theorem subatlas_recognizedAffinoidFamily :
    (a.subatlas P hP).recognizedAffinoidFamily = a.recognizedAffinoidFamily := by
  apply Set.Subset.antisymm
  · rintro S ⟨V, rfl⟩
    exact ⟨a.subatlasReverseRecognizedSubset hP V,
      a.subatlasReverseRecognizedSubset_locus hP V⟩
  · rintro S ⟨V, rfl⟩
    exact ⟨a.subatlasRecognizedSubset hP V, rfl⟩

/-- Whisker the actual forward bounded comparison and then apply the
actual selected counit. This constructs the reverse affinoid comparison
with full naturality, independently of spectrum faithfulness. -/
def subatlasReverseRecognitionAffinoidNatIso :
    a.subatlasReverseRecognitionFunctor hP ⋙
        RecognizedSubset.toAffinoidSpace a.saturatedAtlas ≅
      RecognizedSubset.toAffinoidSpace (a.subatlas P hP).saturatedAtlas :=
  Functor.isoWhiskerLeft (a.subatlasReverseRecognitionFunctor hP)
      (a.subatlasRecognitionAffinoidNatIso hP).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (a.subatlasRecognitionCounitIso hP)
      (RecognizedSubset.toAffinoidSpace (a.subatlas P hP).saturatedAtlas) ≪≫
    (RecognizedSubset.toAffinoidSpace (a.subatlas P hP).saturatedAtlas).leftUnitor

/-- Extract the actual bounded inverse algebra maps from the constructed
reverse natural isomorphism. No identification with another chosen
realization comparison is asserted. -/
def subatlasReverseRecognitionNaturalEquiv
    (V : (a.subatlas P hP).saturatedAtlas.RecognizedSubset) :
    BoundedAlgEquiv K V.algebra (a.subatlasReverseRecognizedSubset hP V).algebra := by
  let e := (a.subatlasReverseRecognitionAffinoidNatIso hP).app V
  exact BoundedAlgEquiv.ofHomInv (Quiver.Hom.unop e.hom) (Quiver.Hom.unop e.inv)
    (fun b => congrArg
      (fun q : Opposite.op V.algebra ⟶ Opposite.op V.algebra =>
        BoundedAlgHom.toAlgHom (Quiver.Hom.unop q) b)
      e.inv_hom_id)
    (fun b => congrArg
      (fun q : Opposite.op (a.subatlasReverseRecognizedSubset hP V).algebra ⟶
        Opposite.op (a.subatlasReverseRecognizedSubset hP V).algebra =>
          BoundedAlgHom.toAlgHom (Quiver.Hom.unop q) b) e.hom_inv_id)

/-- Every reverse recognized inclusion satisfies naturality on the
entire bounded algebra, including all nonreduced information. -/
theorem subatlasReverseRecognitionNaturalEquiv_naturality
    {U V : (a.subatlas P hP).saturatedAtlas.RecognizedSubset} (f : U ⟶ V) :
    (a.subatlasReverseRecognitionNaturalEquiv hP U).toBoundedAlgHom.comp f.restriction =
      ((a.subatlasReverseRecognitionFunctor hP).map f).restriction.comp
        (a.subatlasReverseRecognitionNaturalEquiv hP V).toBoundedAlgHom := by
  exact (congrArg
    (fun q : Opposite.op (a.subatlasReverseRecognizedSubset hP U).algebra ⟶
      Opposite.op V.algebra => Quiver.Hom.unop q)
    ((a.subatlasReverseRecognitionAffinoidNatIso hP).hom.naturality f)).symm

/-- The reverse natural comparison also commutes with the actual ambient
charts on every spectrum point. -/
theorem subatlasReverseRecognitionAffinoidNatIso_over_ambient
    (V : (a.subatlas P hP).saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum (a.subatlasReverseRecognizedSubset hP V).algebra) :
    V.chart ((affinoidSpectrumFunctor K).map
        ((a.subatlasReverseRecognitionAffinoidNatIso hP).hom.app V) x) =
      (a.subatlasReverseRecognizedSubset hP V).chart x := by
  let W := a.subatlasReverseRecognizedSubset hP V
  let e := a.subatlasRecognizedSubsetEquiv hP W
  let y := e.spectrumHomeomorph.symm x
  change V.chart ((a.subatlasRecognitionCounitComponent hP V).hom.spectrumMap y) =
    W.chart x
  exact ((a.subatlasRecognitionCounitComponent hP V).hom.chart_naturality y).trans
    ((a.subatlasRecognizedSubset_chart hP W y).trans
      (congrArg W.chart (e.spectrumHomeomorph.apply_symm_apply x)))

theorem subatlasReverseRecognitionNaturalEquiv_chart
    (V : (a.subatlas P hP).saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum (a.subatlasReverseRecognizedSubset hP V).algebra) :
    (a.subatlasReverseRecognizedSubset hP V).chart x =
      V.chart ((a.subatlasReverseRecognitionNaturalEquiv hP V).spectrumHomeomorph x) :=
  (a.subatlasReverseRecognitionAffinoidNatIso_over_ambient hP V x).symm

end Langlands.Analytic.IndexedAffinoidAtlas
