import Langlands.Geometry.Analytic.AtlasSubatlas
import Langlands.Geometry.Analytic.FullRecognitionStrongInverse

/-! # Recognition invariance for net selections of original charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- The selected original domains form a net on the unchanged space.
This is a condition on the input chart family, not on recognized domains. -/
def IsNetSelection (P : a.Index → Prop) : Prop :=
  AtlasTopology.IsNet (a.selectedChartFamily P)

theorem isNetSelection_of_locallyRefining (P : a.Index → Prop)
    (hP : a.IsLocallyRefiningSelection P) : a.IsNetSelection P :=
  a.isNet_selectedChartFamily P hP

/-- Any original chart subfamily which is a net inherits the actual
algebras, embeddings, restrictions and their full universal properties. -/
def netSubatlas (P : a.Index → Prop) (hP : a.IsNetSelection P) :
    IndexedAffinoidAtlas.{u, v, w} K X where
  Index := {i : a.Index // P i}
  algebra i := a.algebra i.val
  chart i := a.chart i.val
  isEmbedding_chart i := a.isEmbedding_chart i.val
  chartDomain_injective := by
    intro i j hij
    exact Subtype.ext (a.chartDomain_injective hij)
  locallyHausdorff := a.locallyHausdorff
  isNet_chartFamily := hP
  restriction i j h := a.restriction i.val j.val h
  restriction_chart i j h := a.restriction_chart i.val j.val h
  restriction_universal i j h := a.restriction_universal i.val j.val h
  restriction_id i h := a.restriction_id i.val h
  restriction_comp i j k hij hjk hik := a.restriction_comp i.val j.val k.val hij hjk hik

@[simp]
theorem netSubatlas_algebra (P : a.Index → Prop) (hP : a.IsNetSelection P)
    (i : {i : a.Index // P i}) :
    (a.netSubatlas P hP).algebra i = a.algebra i.val := rfl

@[simp]
theorem netSubatlas_chart (P : a.Index → Prop) (hP : a.IsNetSelection P)
    (i : {i : a.Index // P i}) :
    (a.netSubatlas P hP).chart i = a.chart i.val := rfl

@[simp]
theorem netSubatlas_restriction (P : a.Index → Prop) (hP : a.IsNetSelection P)
    (i j : {i : a.Index // P i})
    (h : Set.range ((a.netSubatlas P hP).chart i) ⊆
      Set.range ((a.netSubatlas P hP).chart j)) :
    (a.netSubatlas P hP).restriction i j h = a.restriction i.val j.val h := rfl

theorem netSubatlas_chartFamily (P : a.Index → Prop) (hP : a.IsNetSelection P) :
    Set.range (fun i => Set.range ((a.netSubatlas P hP).chart i)) =
      a.selectedChartFamily P := rfl

/-- The previous locally refining construction is recovered exactly. -/
theorem netSubatlas_eq_subatlas (P : a.Index → Prop)
    (hP : a.IsLocallyRefiningSelection P) :
    a.netSubatlas P (a.isNetSelection_of_locallyRefining P hP) = a.subatlas P hP := rfl

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The actual selected net atlas has the original ambient space. -/
def netSubpresentation (P : A.atlas.Index → Prop) (hP : A.atlas.IsNetSelection P) :
    AffinoidAtlasPresentation.{u, v, w} K where
  space := A.space
  atlas := A.atlas.netSubatlas P hP

namespace StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Source restriction retains every original admissible bounded map;
the selected family need only be a net. -/
def restrictNetSubatlasSource (f : StrongHom A B) (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsNetSelection P) :
    StrongHom (A.netSubpresentation P hP) B where
  baseMap := f.baseMap
  target_exists i := f.target_exists i.val
  pullback i j h := f.pullback i.val j h
  chart_comm i j h x := f.chart_comm i.val j h x
  restriction_comm i i' j j' hi hj h h' :=
    f.restriction_comm i.val i'.val j j' hi hj h h'

@[simp]
theorem restrictNetSubatlasSource_baseMap (f : StrongHom A B)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsNetSelection P) :
    (f.restrictNetSubatlasSource P hP).baseMap = f.baseMap := rfl

@[simp]
theorem restrictNetSubatlasSource_pullback (f : StrongHom A B)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsNetSelection P)
    (i : (A.netSubpresentation P hP).atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i.val) ⊆ Set.range (B.atlas.chart j)) :
    (f.restrictNetSubatlasSource P hP).pullback i j h = f.pullback i.val j h := rfl

theorem IsQuasiIso.restrictNetSubatlasSource {f : StrongHom A B} (hf : f.IsQuasiIso)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsNetSelection P) :
    (f.restrictNetSubatlasSource P hP).IsQuasiIso :=
  ⟨hf.1, fun i j h => hf.2 i.val j h⟩

/-- Coherence is inherited as a law on the unchanged bounded maps,
without any domain-closure premise on the selected atlas. -/
theorem restrictNetSubatlasSource_hasCoherentPullbacks (f : StrongHom A B)
    (hf : f.HasCoherentPullbacks)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsNetSelection P) :
    (f.restrictNetSubatlasSource P hP).HasCoherentPullbacks := by
  intro i j k hj hk
  exact hf i.val j k hj hk

end StrongHom

/-- The identity-space strong inclusion uses the original restrictions
at every admissible pair, including targets outside the selected family. -/
def strongNetSubatlasInclusion (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsNetSelection P) : StrongHom (A.netSubpresentation P hP) A :=
  (StrongHom.id A).restrictNetSubatlasSource P hP

@[simp]
theorem strongNetSubatlasInclusion_baseMap (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsNetSelection P) :
    (A.strongNetSubatlasInclusion P hP).baseMap = ContinuousMap.id A.space := rfl

@[simp]
theorem strongNetSubatlasInclusion_pullback (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsNetSelection P) (i : (A.netSubpresentation P hP).atlas.Index)
    (j : A.atlas.Index)
    (h : (A.strongNetSubatlasInclusion P hP).baseMap ''
      Set.range ((A.netSubpresentation P hP).atlas.chart i) ⊆ Set.range (A.atlas.chart j)) :
    (A.strongNetSubatlasInclusion P hP).pullback i j h =
      A.atlas.restriction i.val j (fun x hx => h ⟨x, hx, rfl⟩) := rfl

theorem isQuasiIso_strongNetSubatlasInclusion (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsNetSelection P) :
    (A.strongNetSubatlasInclusion P hP).IsQuasiIso :=
  (StrongHom.isQuasiIso_id A).restrictNetSubatlasSource P hP

/-- Original identity coherence supplies all coefficient-test chart
compatibility of this inclusion; it is not an additional input. -/
theorem strongNetSubatlasInclusion_hasCoherentPullbacks (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsNetSelection P) :
    (A.strongNetSubatlasInclusion P hP).HasCoherentPullbacks :=
  (StrongHom.id A).restrictNetSubatlasSource_hasCoherentPullbacks
    (StrongHom.hasCoherentPullbacks_id A) P hP

variable (P : A.atlas.Index → Prop) (hP : A.atlas.IsNetSelection P)

/-- The inclusion induces an equivalence on the actual recognized
inclusion categories, with the reverse constructed by full recognition. -/
def netSubatlasRecognitionEquivalence :
    (A.netSubpresentation P hP).atlas.saturatedAtlas.RecognizedSubset ≌
      A.atlas.saturatedAtlas.RecognizedSubset :=
  (A.isQuasiIso_strongNetSubatlasInclusion P hP).generalRecognizedImageEquivalence
    (A.strongNetSubatlasInclusion_hasCoherentPullbacks P hP)

@[simp]
theorem netSubatlasRecognitionEquivalence_functor_locus
    (V : (A.netSubpresentation P hP).atlas.saturatedAtlas.RecognizedSubset) :
    ((A.netSubatlasRecognitionEquivalence P hP).functor.obj V).locus = V.locus := by
  have hl := (A.isQuasiIso_strongNetSubatlasInclusion P hP).recognizedImage_locus
    (A.strongNetSubatlasInclusion_hasCoherentPullbacks P hP) V
  change _ = id '' V.locus at hl
  exact hl.trans (Set.image_id _)

@[simp]
theorem netSubatlasRecognitionEquivalence_inverse_locus
    (W : A.atlas.saturatedAtlas.RecognizedSubset) :
    ((A.netSubatlasRecognitionEquivalence P hP).inverse.obj W).locus = W.locus :=
  (A.isQuasiIso_strongNetSubatlasInclusion P hP).generalReverseRecognizedImage_locus
    (A.strongNetSubatlasInclusion_hasCoherentPullbacks P hP) W

/-- The entire literal family of recognized affinoid subsets is unchanged. -/
theorem netSubatlas_recognizedAffinoidFamily :
    (A.netSubpresentation P hP).atlas.recognizedAffinoidFamily =
      A.atlas.recognizedAffinoidFamily := by
  have hl := (A.isQuasiIso_strongNetSubatlasInclusion P hP).generalRecognizedAffinoidFamily_image
    (A.strongNetSubatlasInclusion_hasCoherentPullbacks P hP)
  change (fun S : Set A.space => id '' S) ''
    (A.netSubpresentation P hP).atlas.recognizedAffinoidFamily =
      A.atlas.recognizedAffinoidFamily at hl
  have hi : (fun S : Set A.space => id '' S) = id := funext Set.image_id
  rw [hi] at hl
  exact (Set.image_id _).symm.trans hl

/-- The forward comparison is natural on complete bounded algebra maps,
not merely on the associated spectrum point maps. -/
def netSubatlasRecognitionAffinoidNatIso :
    (A.netSubatlasRecognitionEquivalence P hP).functor ⋙
        RecognizedSubset.toAffinoidSpace A.atlas.saturatedAtlas ≅
      RecognizedSubset.toAffinoidSpace
        (A.netSubpresentation P hP).atlas.saturatedAtlas :=
  (A.isQuasiIso_strongNetSubatlasInclusion P hP).recognizedImageAffinoidNatIso
    (A.strongNetSubatlasInclusion_hasCoherentPullbacks P hP)

/-- The reverse comparison retains the actual bounded inverse diagrams
and their full naturality. -/
def netSubatlasReverseRecognitionAffinoidNatIso :
    (A.netSubatlasRecognitionEquivalence P hP).inverse ⋙
        RecognizedSubset.toAffinoidSpace
          (A.netSubpresentation P hP).atlas.saturatedAtlas ≅
      RecognizedSubset.toAffinoidSpace A.atlas.saturatedAtlas :=
  (A.isQuasiIso_strongNetSubatlasInclusion P hP).generalReverseRecognizedImageAffinoidNatIso
    (A.strongNetSubatlasInclusion_hasCoherentPullbacks P hP)

/-- Full recognition gives an isomorphism in the actual saturated strong
category, with all admissible pullbacks and both entire inverse identities. -/
def netSubatlasFullRecognitionStrongIso :
    SaturatedAtlasPresentation.ofFullRecognition (A.netSubpresentation P hP) ≅
      SaturatedAtlasPresentation.ofFullRecognition A :=
  (A.isQuasiIso_strongNetSubatlasInclusion P hP).fullRecognitionStrongIso
    (A.strongNetSubatlasInclusion_hasCoherentPullbacks P hP)

@[simp]
theorem netSubatlasFullRecognitionStrongIso_hom_baseMap :
    (A.netSubatlasFullRecognitionStrongIso P hP).hom.baseMap =
      ContinuousMap.id A.space := rfl

@[simp]
theorem netSubatlasFullRecognitionStrongIso_inv_baseMap :
    (A.netSubatlasFullRecognitionStrongIso P hP).inv.baseMap =
      ContinuousMap.id A.space := by
  ext x
  exact (A.isQuasiIso_strongNetSubatlasInclusion P hP).baseMap_inverseBaseMap x

end AffinoidAtlasPresentation

end Langlands.Analytic
