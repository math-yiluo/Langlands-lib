import Langlands.AlgebraicGeometry.Picard.DeterminantFrames
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleRefinement
import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing

/-! # Determinant comparison across different open covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.DeterminantFrames

open Langlands.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules} {ι κ μ I : Type u}
  [Fintype I] {T : ι → X.Opens} {S : κ → X.Opens} {R : μ → X.Opens}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i)) I ≅ M.over (T i))
  (f : ∀ j, SheafOfModules.free (R := X.ringCatSheaf.over (S j)) I ≅ M.over (S j))
  (g : ∀ k, SheafOfModules.free (R := X.ringCatSheaf.over (R k)) I ≅ M.over (R k))

private local instance : DecidableEq I := Classical.decEq I

/-- Determinant transitions of a selected subfamily are the refined transitions. -/
lemma refineCocycle_reindex (β : κ → ι) :
    CocycleGluing.refineCocycle (S := fun j => T (β j)) (cocycle e) β
        (fun _ => le_rfl) =
      cocycle (fun j => e (β j)) := by
  funext i j
  apply Units.ext
  change X.presheaf.map (𝟙 (op (T (β i) ⊓ T (β j))))
      (unit e (β i) (β j) inf_le_left inf_le_right).val = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The original determinant generators, indexed by a selected subfamily. -/
def reindexFrame (β : κ → ι) (j : κ) :
    Γ(CocycleGluing.glued (cocycle e), T (β j)) :=
  CocycleGluing.refineFrame (cocycle e) (isCocycle e) β (fun _ => le_rfl) j

lemma isFrameOn_reindexFrame (β : κ → ι) (j : κ) :
    Scheme.Modules.IsFrameOn (reindexFrame e β j) (T (β j)) :=
  CocycleGluing.isFrameOn_refineFrame (cocycle e) (isCocycle e) β
    (fun _ => le_rfl) j

lemma isTransition_reindexFrame (β : κ → ι) :
    CocycleGluing.IsTransition (reindexFrame e β) (cocycle (fun j => e (β j))) := by
  rw [← refineCocycle_reindex e β]
  exact CocycleGluing.isTransition_refineFrame (cocycle e) (isCocycle e) β
    (fun _ => le_rfl)

/-- A covering selected subfamily gives the same actual determinant sheaf. -/
def reindexIso (β : κ → ι) (hβ : (⨆ j, T (β j)) = ⊤) :
    CocycleGluing.glued (cocycle e) ≅ CocycleGluing.glued (cocycle (fun j => e (β j))) :=
  CocycleGluing.frameIso (isFrameOn_reindexFrame e β) (isTransition_reindexFrame e β) hβ

lemma reindexIso_hom_app_genSec (β : κ → ι) (hβ : (⨆ j, T (β j)) = ⊤)
    (j : κ) {V : X.Opens} (hV : V ≤ T (β j)) :
    (reindexIso e β hβ).hom.app V
        (CocycleGluing.genSec (cocycle e) (isCocycle e) (β j) hV) =
      CocycleGluing.genSec (cocycle (fun j => e (β j)))
        (isCocycle (fun j => e (β j))) j hV := by
  have h := CocycleGluing.frameIso_hom_app_frame (isFrameOn_reindexFrame e β)
    (isTransition_reindexFrame e β) hβ (isCocycle (fun j => e (β j))) j hV
  simpa only [reindexIso, reindexFrame, CocycleGluing.refineFrame,
    CocycleGluing.map_genSec] using h

lemma reindexIso_inv_app_genSec (β : κ → ι) (hβ : (⨆ j, T (β j)) = ⊤)
    (j : κ) {V : X.Opens} (hV : V ≤ T (β j)) :
    (reindexIso e β hβ).inv.app V
        (CocycleGluing.genSec (cocycle (fun j => e (β j)))
          (isCocycle (fun j => e (β j))) j hV) =
      CocycleGluing.genSec (cocycle e) (isCocycle e) (β j) hV := by
  have h := CocycleGluing.frameIso_inv_app_genSec (isFrameOn_reindexFrame e β)
    (isTransition_reindexFrame e β) hβ (isCocycle (fun j => e (β j))) j hV
  simpa only [reindexIso, reindexFrame, CocycleGluing.refineFrame,
    CocycleGluing.map_genSec] using h

/-- The two frame families on the disjoint union of their chart index types. -/
def sumFrames (i : ι ⊕ κ) :
    SheafOfModules.free (R := X.ringCatSheaf.over (Sum.elim T S i)) I ≅
      M.over (Sum.elim T S i) :=
  Sum.rec e f i

/-- Determinant comparison through the common family containing both covers. -/
def coverChangeIso (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) :
    CocycleGluing.glued (cocycle e) ≅ CocycleGluing.glued (cocycle f) :=
  (reindexIso (sumFrames e f) Sum.inl hT).symm ≪≫
    reindexIso (sumFrames e f) Sum.inr hS

/-- The mixed determinant on an open inside both charts. -/
def coverChangeUnit (i : ι) (j : κ) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ S j) : (Γ(X, V))ˣ :=
  unit (sumFrames e f) (Sum.inr j) (Sum.inl i) (U := V) hj hi

/-- The cover comparison has the expected determinant formula on every overlap. -/
lemma coverChangeIso_hom_app_genSec
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤)
    (i : ι) (j : κ) {V : X.Opens} (hi : V ≤ T i) (hj : V ≤ S j) :
    (coverChangeIso e f hT hS).hom.app V
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi) =
      (coverChangeUnit e f i j hi hj : Γ(X, V)) •
        CocycleGluing.genSec (cocycle f) (isCocycle f) j hj := by
  have hleft :
      (reindexIso (sumFrames e f) Sum.inl hT).inv.app V
          (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi) =
        CocycleGluing.genSec (cocycle (sumFrames e f))
          (isCocycle (sumFrames e f)) (Sum.inl i) hi :=
    reindexIso_inv_app_genSec (sumFrames e f) Sum.inl hT i hi
  have hright :
      (reindexIso (sumFrames e f) Sum.inr hS).hom.app V
          (CocycleGluing.genSec (cocycle (sumFrames e f))
            (isCocycle (sumFrames e f)) (Sum.inr j) hj) =
        CocycleGluing.genSec (cocycle f) (isCocycle f) j hj :=
    reindexIso_hom_app_genSec (sumFrames e f) Sum.inr hS j hj
  have hgen := CocycleGluing.genSec_eq_smul_genSec
    (isCocycle (sumFrames e f)) (i := Sum.inr j) (j := Sum.inl i) hj hi
  have hunit := unit_restrict (sumFrames e f) (Sum.inr j) (Sum.inl i)
    inf_le_left inf_le_right (le_inf hj hi)
  change (reindexIso (sumFrames e f) Sum.inr hS).hom.app V
      ((reindexIso (sumFrames e f) Sum.inl hT).inv.app V
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)) = _
  calc
    _ = (reindexIso (sumFrames e f) Sum.inr hS).hom.app V
        (CocycleGluing.genSec (cocycle (sumFrames e f))
          (isCocycle (sumFrames e f)) (Sum.inl i) hi) := congrArg _ hleft
    _ = (reindexIso (sumFrames e f) Sum.inr hS).hom.app V
        ((coverChangeUnit e f i j hi hj).val •
          CocycleGluing.genSec (cocycle (sumFrames e f))
            (isCocycle (sumFrames e f)) (Sum.inr j) hj) := by
      apply congrArg
      exact hgen.trans (congrArg (fun a => a • _) hunit)
    _ = _ := by
      rw [Scheme.Modules.Hom.app_smul]
      exact congrArg (fun m => (coverChangeUnit e f i j hi hj).val • m) hright

lemma coverChangeUnit_self (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    (coverChangeUnit e e i i hi hi : Γ(X, V)) = 1 := by
  change ((basis e i hi).toMatrix (basis e i hi)).det = 1
  rw [Module.Basis.toMatrix_self, Matrix.det_one]

/-- The mixed comparison determinants compose on every common open. -/
lemma coverChangeUnit_mul (i : ι) (j : κ) (k : μ) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ S j) (hk : V ≤ R k) :
    (coverChangeUnit e f i j hi hj : Γ(X, V)) *
        (coverChangeUnit f g j k hj hk : Γ(X, V)) =
      (coverChangeUnit e g i k hi hk : Γ(X, V)) := by
  change ((basis f j hj).toMatrix (basis e i hi)).det *
      ((basis g k hk).toMatrix (basis f j hj)).det =
    ((basis g k hk).toMatrix (basis e i hi)).det
  rw [mul_comm, ← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix]

@[simp]
lemma coverChangeIso_self (hT : (⨆ i, T i) = ⊤) :
    coverChangeIso e e hT hT = Iso.refl _ := by
  apply Iso.ext
  apply CocycleGluing.hom_ext_genSec (isCocycle e)
  intro i V hi
  rw [coverChangeIso_hom_app_genSec e e hT hT i i hi hi,
    coverChangeUnit_self, one_smul]
  rfl

/-- Cover comparison is transitive as an equality of actual sheaf isomorphisms. -/
lemma coverChangeIso_trans (hT : (⨆ i, T i) = ⊤)
    (hS : (⨆ j, S j) = ⊤) (hR : (⨆ k, R k) = ⊤) :
    coverChangeIso e f hT hS ≪≫ coverChangeIso f g hS hR =
      coverChangeIso e g hT hR := by
  have hmem {ν : Type u} {W : ν → X.Opens} (hW : (⨆ i, W i) = ⊤)
      (x : X) : ∃ i, x ∈ W i := by
    apply Opens.mem_iSup.mp
    rw [hW]
    trivial
  apply Iso.ext
  apply OpenCoverHomGluing.hom_ext_of_local
    (V := fun q : ι × κ × μ => T q.1 ⊓ S q.2.1 ⊓ R q.2.2)
    (fun x => by
      obtain ⟨i, hi⟩ := hmem hT x
      obtain ⟨j, hj⟩ := hmem hS x
      obtain ⟨k, hk⟩ := hmem hR x
      exact ⟨(i, j, k), ⟨⟨hi, hj⟩, hk⟩⟩)
  intro q P hP
  have hi : P ≤ T q.1 := hP.trans (inf_le_left.trans inf_le_left)
  have hj : P ≤ S q.2.1 := hP.trans (inf_le_left.trans inf_le_right)
  have hk : P ≤ R q.2.2 := hP.trans inf_le_right
  ext m
  obtain ⟨r, rfl⟩ := (CocycleGluing.smul_genSec_bijective
    (cocycle e) (isCocycle e) q.1 hi).2 m
  change (coverChangeIso f g hS hR).hom.app P
      ((coverChangeIso e f hT hS).hom.app P
        (r • CocycleGluing.genSec (cocycle e) (isCocycle e) q.1 hi)) = _
  rw [Scheme.Modules.Hom.app_smul,
    coverChangeIso_hom_app_genSec e f hT hS q.1 q.2.1 hi hj,
    Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul,
    coverChangeIso_hom_app_genSec f g hS hR q.2.1 q.2.2 hj hk,
    Scheme.Modules.Hom.app_smul,
    coverChangeIso_hom_app_genSec e g hT hR q.1 q.2.2 hi hk]
  simp only [smul_smul]
  rw [coverChangeUnit_mul]

/-- The comparison as an isomorphism of actual line bundles. -/
def lineBundleCoverChangeIso (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) :
    lineBundle e hT ≅ lineBundle f hS :=
  ObjectProperty.isoMk _ (coverChangeIso e f hT hS)

@[simp]
lemma lineBundleCoverChangeIso_self (hT : (⨆ i, T i) = ⊤) :
    lineBundleCoverChangeIso e e hT hT = Iso.refl _ := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (coverChangeIso_self e hT)

lemma lineBundleCoverChangeIso_trans (hT : (⨆ i, T i) = ⊤)
    (hS : (⨆ j, S j) = ⊤) (hR : (⨆ k, R k) = ⊤) :
    lineBundleCoverChangeIso e f hT hS ≪≫ lineBundleCoverChangeIso f g hS hR =
      lineBundleCoverChangeIso e g hT hR := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (coverChangeIso_trans e f g hT hS hR)

end Langlands.AlgebraicGeometry.Picard.DeterminantFrames
