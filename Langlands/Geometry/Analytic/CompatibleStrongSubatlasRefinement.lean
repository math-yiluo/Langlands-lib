import Langlands.Geometry.Analytic.StrongSubatlasSourceRefinement
import Langlands.Geometry.Analytic.CompatibleStrongQuasiIsomorphisms
import Mathlib.CategoryTheory.CommSq

/-! # Actual compatible strong refinement squares for target subatlases -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- Source selection retains the original all-coefficient coherence law. -/
theorem hasCoherentPullbacks_restrictSubatlasSource (f : StrongHom A B)
    (hf : f.HasCoherentPullbacks) (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) :
    (f.restrictSubatlasSource P hP).HasCoherentPullbacks := by
  intro i j k hj hk
  exact hf i.val j k hj hk

/-- The constructed lift retains coherence on every selected target test. -/
theorem hasCoherentPullbacks_targetSubatlasLift (f : StrongHom A B)
    (hf : f.HasCoherentPullbacks) (ha : A.atlas.HasAllLocalDomains)
    (P : B.atlas.Index → Prop) (hP : B.atlas.IsLocallyRefiningSelection P) :
    (f.targetSubatlasLift ha P hP).HasCoherentPullbacks := by
  intro i j k hj hk T η m hmj hmk α hα
  exact hf i.val j.val k.val hj hk T η m.val hmj hmk α hα

end StrongHom

/-- The actual original bounded restrictions give a compatible inclusion,
without any source domain-closure premise. -/
def compatibleSubatlasInclusion (A : AffinoidAtlasPresentation.{u, v, w} K)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P) :
    CompatibleStrongHom (A.subpresentation P hP) A where
  toStrongHom := A.strongSubatlasInclusion P hP
  compatible := StrongHom.hasLocallyCompatiblePullbacks_iff _ |>.mpr
    ((StrongHom.id A).hasCoherentPullbacks_restrictSubatlasSource
      (StrongHom.hasCoherentPullbacks_id A) P hP)

@[simp]
theorem compatibleSubatlasInclusion_toStrongHom (A : AffinoidAtlasPresentation.{u, v, w} K)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P) :
    (A.compatibleSubatlasInclusion P hP).toStrongHom = A.strongSubatlasInclusion P hP := rfl

@[simp]
theorem compatibleSubatlasInclusion_baseMap (A : AffinoidAtlasPresentation.{u, v, w} K)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P) :
    (A.compatibleSubatlasInclusion P hP).baseMap = ContinuousMap.id A.space := rfl

theorem isQuasiIso_compatibleSubatlasInclusion (A : AffinoidAtlasPresentation.{u, v, w} K)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P) :
    (A.compatibleSubatlasInclusion P hP).toStrongHom.IsQuasiIso :=
  A.isQuasiIso_strongSubatlasInclusion P hP

namespace CompatibleStrongHom

/-- Restrict a compatible map to a locally refining original source atlas,
retaining all of its admissible original bounded pullbacks. -/
def restrictSubatlasSource (f : CompatibleStrongHom A B) (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) :
    CompatibleStrongHom (A.subpresentation P hP) B where
  toStrongHom := f.toStrongHom.restrictSubatlasSource P hP
  compatible := StrongHom.hasLocallyCompatiblePullbacks_iff _ |>.mpr
    (f.toStrongHom.hasCoherentPullbacks_restrictSubatlasSource f.coherent P hP)

@[simp]
theorem restrictSubatlasSource_baseMap (f : CompatibleStrongHom A B)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P) :
    (f.restrictSubatlasSource P hP).baseMap = f.baseMap := rfl

@[simp]
theorem restrictSubatlasSource_pullback (f : CompatibleStrongHom A B)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P)
    (i : (A.subpresentation P hP).atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i.val) ⊆ Set.range (B.atlas.chart j)) :
    (f.restrictSubatlasSource P hP).pullback i j h = f.pullback i.val j h := rfl

/-- The compatible composite with the source inclusion recovers the entire
restricted map, including every bounded pullback. -/
theorem subatlasInclusion_comp (f : CompatibleStrongHom A B)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P) :
    (A.compatibleSubatlasInclusion P hP).comp f = f.restrictSubatlasSource P hP := by
  refine ext_of_pullback rfl ?_
  intro i
  obtain ⟨j, hj⟩ := f.target_exists i.val
  refine ⟨j, hj, ?_⟩
  have hi : (A.compatibleSubatlasInclusion P hP).baseMap ''
      Set.range ((A.subpresentation P hP).atlas.chart i) ⊆
        Set.range (A.atlas.chart i.val) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  rw [comp_pullback _ f i i.val j hi hj hj]
  change (A.atlas.restriction i.val i.val _).comp (f.pullback i.val j hj) =
    f.pullback i.val j hj
  rw [A.atlas.restriction_id, BoundedAlgHom.id_comp]

/-- The actual source-refinement construction carries compatible strong maps. -/
def targetSubatlasLift (f : CompatibleStrongHom A B) (ha : A.atlas.HasAllLocalDomains)
    (P : B.atlas.Index → Prop) (hP : B.atlas.IsLocallyRefiningSelection P) :
    CompatibleStrongHom (f.toStrongHom.targetSubatlasSource ha P hP)
      (B.subpresentation P hP) where
  toStrongHom := f.toStrongHom.targetSubatlasLift ha P hP
  compatible := StrongHom.hasLocallyCompatiblePullbacks_iff _ |>.mpr
    (f.toStrongHom.hasCoherentPullbacks_targetSubatlasLift f.coherent ha P hP)

@[simp]
theorem targetSubatlasLift_toStrongHom (f : CompatibleStrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) (P : B.atlas.Index → Prop)
    (hP : B.atlas.IsLocallyRefiningSelection P) :
    (f.targetSubatlasLift ha P hP).toStrongHom =
      f.toStrongHom.targetSubatlasLift ha P hP := rfl

@[simp]
theorem targetSubatlasLift_baseMap (f : CompatibleStrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) (P : B.atlas.Index → Prop)
    (hP : B.atlas.IsLocallyRefiningSelection P) :
    (f.targetSubatlasLift ha P hP).baseMap = f.baseMap := rfl

@[simp]
theorem targetSubatlasLift_pullback (f : CompatibleStrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) (P : B.atlas.Index → Prop)
    (hP : B.atlas.IsLocallyRefiningSelection P)
    (i : (f.toStrongHom.targetSubatlasSource ha P hP).atlas.Index)
    (j : (B.subpresentation P hP).atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i.val) ⊆ Set.range (B.atlas.chart j.val)) :
    (f.targetSubatlasLift ha P hP).pullback i j h = f.pullback i.val j.val h := rfl

/-- The other route also recovers the entire restricted original map.
The proof computes a complete bounded composite through a selected chart. -/
theorem targetSubatlasLift_comp_inclusion (f : CompatibleStrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) (P : B.atlas.Index → Prop)
    (hP : B.atlas.IsLocallyRefiningSelection P) :
    (f.targetSubatlasLift ha P hP).comp (B.compatibleSubatlasInclusion P hP) =
      f.restrictSubatlasSource (f.toStrongHom.sourceSelectionForTarget P)
        (f.toStrongHom.sourceSelectionForTarget_locallyRefining ha P hP) := by
  refine ext_of_pullback rfl ?_
  intro i
  obtain ⟨j, hPj, hj⟩ := i.property
  let J : (B.subpresentation P hP).atlas.Index := ⟨j, hPj⟩
  have hJ : (B.compatibleSubatlasInclusion P hP).baseMap ''
      Set.range ((B.subpresentation P hP).atlas.chart J) ⊆ Set.range (B.atlas.chart j) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine ⟨j, hj, ?_⟩
  rw [comp_pullback (f.targetSubatlasLift ha P hP)
    (B.compatibleSubatlasInclusion P hP) i J j hj hJ hj]
  change (f.pullback i.val j hj).comp (B.atlas.restriction j j _) =
    f.pullback i.val j hj
  rw [B.atlas.restriction_id, BoundedAlgHom.comp_id]

/-- The actual compatible refinement square commutes as full strong maps. -/
theorem targetSubatlasLift_square (f : CompatibleStrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) (P : B.atlas.Index → Prop)
    (hP : B.atlas.IsLocallyRefiningSelection P) :
    (f.targetSubatlasLift ha P hP).comp (B.compatibleSubatlasInclusion P hP) =
      (A.compatibleSubatlasInclusion (f.toStrongHom.sourceSelectionForTarget P)
        (f.toStrongHom.sourceSelectionForTarget_locallyRefining ha P hP)).comp f :=
  (f.targetSubatlasLift_comp_inclusion ha P hP).trans (f.subatlasInclusion_comp _ _).symm

/-- Full affinoid-test quasi-isomorphisms remain so in the compatible lift. -/
theorem isQuasiIso_targetSubatlasLift (f : CompatibleStrongHom A B)
    (hf : f.toStrongHom.IsQuasiIso) (ha : A.atlas.HasAllLocalDomains)
    (P : B.atlas.Index → Prop) (hP : B.atlas.IsLocallyRefiningSelection P) :
    (f.targetSubatlasLift ha P hP).toStrongHom.IsQuasiIso :=
  hf.targetSubatlasLift ha P hP

end CompatibleStrongHom
end AffinoidAtlasPresentation

namespace CompatibleAtlasPresentation

/-- The constructed square lives in the actual compatible-map category.
Both vertical inclusions are full quasi-isomorphisms. -/
theorem targetSubatlas_commSq {A B : CompatibleAtlasPresentation.{u, v, w} K}
    (f : A ⟶ B) (ha : A.presentation.atlas.HasAllLocalDomains)
    (P : B.presentation.atlas.Index → Prop)
    (hP : B.presentation.atlas.IsLocallyRefiningSelection P) :
    CommSq (C := CompatibleAtlasPresentation.{u, v, w} K)
      (show (⟨f.toStrongHom.targetSubatlasSource ha P hP⟩ :
          CompatibleAtlasPresentation.{u, v, w} K) ⟶
          ⟨B.presentation.subpresentation P hP⟩ from f.targetSubatlasLift ha P hP)
      (A.presentation.compatibleSubatlasInclusion (f.toStrongHom.sourceSelectionForTarget P)
        (f.toStrongHom.sourceSelectionForTarget_locallyRefining ha P hP))
      (B.presentation.compatibleSubatlasInclusion P hP) f :=
  ⟨f.targetSubatlasLift_square ha P hP⟩

end CompatibleAtlasPresentation
end Langlands.Analytic
