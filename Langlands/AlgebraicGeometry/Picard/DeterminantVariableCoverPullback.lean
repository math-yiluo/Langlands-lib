import Langlands.AlgebraicGeometry.Picard.DeterminantVariableNaturality

/-! # Variable-rank determinant cover comparison and pullback -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames
open Langlands.Scheme.Modules
variable {X Y : Scheme.{u}} {M : X.Modules} {ι κ : Type u}
  {T : ι → X.Opens} {S : κ → X.Opens} {n : ι → ℕ} {m : κ → ℕ}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
    (ULift.{u} (Fin (n i))) ≅ M.over (T i))
  (d : ∀ j, SheafOfModules.free (R := X.ringCatSheaf.over (S j))
    (ULift.{u} (Fin (m j))) ≅ M.over (S j))

lemma hom_ext_genSec_overlap
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) {P : X.Modules}
    {a b : CocycleGluing.glued (cocycle e) ⟶ P}
    (h : ∀ (i : ι) (j : κ) (V : X.Opens) (hi : V ≤ T i) (_hj : V ≤ S j),
      a.app V (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi) =
      b.app V (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)) : a = b := by
  apply OpenCoverHomGluing.hom_ext_of_local
    (V := fun z : ι × κ => T z.1 ⊓ S z.2) (fun x => by
      have ht : ∃ i, x ∈ T i := Opens.mem_iSup.mp (by rw [hT]; trivial)
      have hs : ∃ j, x ∈ S j := Opens.mem_iSup.mp (by rw [hS]; trivial)
      obtain ⟨i, hi⟩ := ht
      obtain ⟨j, hj⟩ := hs
      exact ⟨(i, j), hi, hj⟩)
  intro z V hV
  have hi : V ≤ T z.1 := hV.trans inf_le_left
  have hj : V ≤ S z.2 := hV.trans inf_le_right
  ext m
  obtain ⟨r, rfl⟩ := (CocycleGluing.smul_genSec_bijective
    (cocycle e) (isCocycle e) z.1 hi).2 m
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, h z.1 z.2 V hi hj]

lemma isoUnit_refl_coverChange (i : ι) (j : κ) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ S j) :
    (isoUnit e d (Iso.refl M) i j hi hj : Γ(X, V)) =
      (coverChangeUnit e d i j hi hj : Γ(X, V)) := by
  rw [isoUnit_eq]
  have hb : (basis e i hi).map (DeterminantFrames.sectionLinearEquiv (Iso.refl M) V) =
      basis e i hi := by
    ext a
    rfl
  rw [hb]
  rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
lemma isoMap_refl_coverChange
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) :
    isoMap e d (Iso.refl M) hT hS = coverChangeIso e d hT hS := by
  apply Iso.ext
  apply hom_ext_genSec_overlap e hT hS
  intro i j V hi hj
  rw [isoMap_hom_app_genSec e d (Iso.refl M) hT hS i j hi hj,
    coverChangeIso_hom_app_genSec e d hT hS i j hi hj,
    isoUnit_refl_coverChange]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
lemma pullbackIso_coverChange (q : Y ⟶ X)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) :
    (Scheme.Modules.pullback q).mapIso (coverChangeIso e d hT hS) ≪≫
        pullbackIso d q hS =
      pullbackIso e q hT ≪≫
        coverChangeIso (pullbackFrames e q) (pullbackFrames d q)
          (q.iSup_preimage_eq_top hT) (q.iSup_preimage_eq_top hS) := by
  have h := pullbackIso_naturality e d q (Iso.refl M) hT hS
  rw [isoMap_refl_coverChange, Functor.mapIso_refl, isoMap_refl_coverChange] at h
  exact h

lemma lineBundleIsoMap_refl_coverChange
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) :
    lineBundleIsoMap e d (Iso.refl M) hT hS =
      lineBundleCoverChangeIso e d hT hS := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (isoMap_refl_coverChange e d hT hS)

/-- The cover comparison constructed directly from the two pulled-back
frame systems. -/
def lineBundlePullbackCoverChangeIso (q : Y ⟶ X)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) :
    lineBundle (pullbackFrames e q) (q.iSup_preimage_eq_top hT) ≅
      lineBundle (pullbackFrames d q) (q.iSup_preimage_eq_top hS) :=
  lineBundleCoverChangeIso (pullbackFrames e q) (pullbackFrames d q)
    (q.iSup_preimage_eq_top hT) (q.iSup_preimage_eq_top hS)

lemma lineBundlePullbackIso_coverChange (q : Y ⟶ X)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) :
    (LineBundle.pullback q).mapIso (lineBundleCoverChangeIso e d hT hS) ≪≫
        lineBundlePullbackIso d q hS =
      lineBundlePullbackIso e q hT ≪≫
        lineBundlePullbackCoverChangeIso e d q hT hS := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (pullbackIso_coverChange e d q hT hS)

end Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames
