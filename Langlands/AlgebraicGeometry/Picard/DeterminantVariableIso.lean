import Langlands.AlgebraicGeometry.Picard.DeterminantVariableCover
import Langlands.AlgebraicGeometry.Picard.DeterminantIso

/-! # Variable-rank determinant maps for actual module-sheaf isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames

open Langlands.Scheme.Modules
open DeterminantFrames (sectionLinearEquiv eqToIso_hom_app_genSec)

/-- A linear equivalence preserves the mixed determinant unit of two bases. -/
lemma mixedUnit_map {A B R : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    {r s : ℕ} (a : Module.Basis (Fin r) R A) (b : Module.Basis (Fin s) R A)
    (φ : A ≃ₗ[R] B) :
    Langlands.LinearAlgebra.FiniteBasisDeterminant.unit (a.map φ) (b.map φ) =
      Langlands.LinearAlgebra.FiniteBasisDeterminant.unit a b := by
  apply Units.ext
  symm
  apply Langlands.LinearAlgebra.FiniteBasisDeterminant.map_unit (RingHom.id R)
  intro i j
  change a.repr (b j) i = a.repr (φ.symm (φ (b j))) i
  rw [LinearEquiv.symm_apply_apply]

variable {X : Scheme.{u}} {M N P : X.Modules} {ι κ μ : Type u}
  {T : ι → X.Opens} {S : κ → X.Opens} {R : μ → X.Opens}
  {n : ι → ℕ} {m : κ → ℕ} {l : μ → ℕ}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
    (ULift.{u} (Fin (n i))) ≅ M.over (T i))
  (f : ∀ j, SheafOfModules.free (R := X.ringCatSheaf.over (S j))
    (ULift.{u} (Fin (m j))) ≅ N.over (S j))
  (g : ∀ k, SheafOfModules.free (R := X.ringCatSheaf.over (R k))
    (ULift.{u} (Fin (l k))) ≅ P.over (R k))

/-- Transport actual frames, retaining the finite rank of each chart. -/
def mapFrames (φ : M ≅ N) (i : ι) :
    SheafOfModules.free (R := X.ringCatSheaf.over (T i))
      (ULift.{u} (Fin (n i))) ≅ N.over (T i) :=
  e i ≪≫ (SheafOfModules.overFunctor X.ringCatSheaf (T i)).mapIso φ

lemma basis_mapFrames (φ : M ≅ N) (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    basis (mapFrames e φ) i hi = (basis e i hi).map (sectionLinearEquiv φ V) := by
  ext a
  simp only [Module.Basis.map_apply, basis_apply]
  calc
    _ = (localBasisSection (mapFrames e φ i) ⟨a⟩).val
        (op (Over.mk (homOfLE hi))) :=
      localSectionBasis_apply (mapFrames e φ i) (Over.mk (homOfLE hi)) ⟨a⟩
    _ = (sectionLinearEquiv φ V)
        ((localBasisSection (e i) ⟨a⟩).val (op (Over.mk (homOfLE hi)))) :=
      congrArg (fun s => s.val (op (Over.mk (homOfLE hi))))
        (SheafOfModules.freeHomEquiv_comp_apply (e i).hom
          ((SheafOfModules.overFunctor X.ringCatSheaf (T i)).map φ.hom) ⟨a⟩)
    _ = _ := congrArg (sectionLinearEquiv φ V)
      (localSectionBasis_apply (e i) (Over.mk (homOfLE hi)) ⟨a⟩).symm

lemma unit_mapFrames (φ : M ≅ N) (i j : ι) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ T j) :
    unit (mapFrames e φ) i j hi hj = unit e i j hi hj := by
  unfold unit
  rw [basis_mapFrames, basis_mapFrames]
  exact mixedUnit_map _ _ _

/-- Transporting every frame preserves the actual determinant cocycle. -/
lemma cocycle_mapFrames (φ : M ≅ N) : cocycle (mapFrames e φ) = cocycle e := by
  funext i j
  exact unit_mapFrames e φ i j inf_le_left inf_le_right

/-- Compare to the transported frame presentation of the determinant sheaf. -/
def mapFramesIso (φ : M ≅ N) :
    CocycleGluing.glued (cocycle e) ≅ CocycleGluing.glued (cocycle (mapFrames e φ)) :=
  eqToIso (congrArg CocycleGluing.glued (cocycle_mapFrames e φ).symm)

set_option maxHeartbeats 800000 in
lemma mapFramesIso_hom_app_genSec (φ : M ≅ N)
    (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    (mapFramesIso e φ).hom.app V (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi) =
      CocycleGluing.genSec (cocycle (mapFrames e φ)) (isCocycle (mapFrames e φ)) i hi :=
  eqToIso_hom_app_genSec (cocycle_mapFrames e φ).symm _ _ i hi

/-- The mixed determinant of the actual isomorphism in the supplied frames. -/
def isoUnit (φ : M ≅ N) (i : ι) (j : κ) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ S j) : (Γ(X, V))ˣ :=
  coverChangeUnit (mapFrames e φ) f i j hi hj

lemma isoUnit_eq (φ : M ≅ N) (i : ι) (j : κ) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ S j) :
    isoUnit e f φ i j hi hj =
      Langlands.LinearAlgebra.FiniteBasisDeterminant.unit
        (basis f j hj) ((basis e i hi).map (sectionLinearEquiv φ V)) := by
  change Langlands.LinearAlgebra.FiniteBasisDeterminant.unit
    (basis f j hj) (basis (mapFrames e φ) i hi) = _
  rw [basis_mapFrames]

lemma isoUnit_self (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    (isoUnit e e (Iso.refl M) i i hi hi : Γ(X, V)) = 1 := by
  rw [isoUnit_eq]
  have hb : (basis e i hi).map (sectionLinearEquiv (Iso.refl M) V) =
      basis e i hi := by
    ext a
    rfl
  rw [hb, Langlands.LinearAlgebra.FiniteBasisDeterminant.unit_self, Units.val_one]

lemma isoUnit_comp (φ : M ≅ N) (ψ : N ≅ P)
    (i : ι) (j : κ) (k : μ) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ S j) (hk : V ≤ R k) :
    (isoUnit e f φ i j hi hj : Γ(X, V)) *
        (isoUnit f g ψ j k hj hk : Γ(X, V)) =
      (isoUnit e g (φ ≪≫ ψ) i k hi hk : Γ(X, V)) := by
  rw [isoUnit_eq, isoUnit_eq, isoUnit_eq]
  have hb : (basis e i hi).map (sectionLinearEquiv (φ ≪≫ ψ) V) =
      ((basis e i hi).map (sectionLinearEquiv φ V)).map
        (sectionLinearEquiv ψ V) := by
    ext a
    rfl
  rw [hb, ← mixedUnit_map (basis f j hj)
    ((basis e i hi).map (sectionLinearEquiv φ V)) (sectionLinearEquiv ψ V), mul_comm]
  exact congrArg Units.val
    (Langlands.LinearAlgebra.FiniteBasisDeterminant.unit_mul _ _ _)

/-- The determinant isomorphism induced by an actual isomorphism of module sheaves. -/
def isoMap (φ : M ≅ N) (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) :
    CocycleGluing.glued (cocycle e) ≅ CocycleGluing.glued (cocycle f) :=
  mapFramesIso e φ ≪≫ coverChangeIso (mapFrames e φ) f hT hS

lemma isoMap_hom_app_genSec (φ : M ≅ N)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤)
    (i : ι) (j : κ) {V : X.Opens} (hi : V ≤ T i) (hj : V ≤ S j) :
    (isoMap e f φ hT hS).hom.app V
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi) =
      (isoUnit e f φ i j hi hj : Γ(X, V)) •
        CocycleGluing.genSec (cocycle f) (isCocycle f) j hj := by
  change (coverChangeIso (mapFrames e φ) f hT hS).hom.app V
      ((mapFramesIso e φ).hom.app V
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)) = _
  rw [mapFramesIso_hom_app_genSec]
  exact coverChangeIso_hom_app_genSec (mapFrames e φ) f hT hS i j hi hj

@[simp]
lemma isoMap_refl (hT : (⨆ i, T i) = ⊤) :
    isoMap e e (Iso.refl M) hT hT = Iso.refl _ := by
  apply Iso.ext
  apply CocycleGluing.hom_ext_genSec (isCocycle e)
  intro i V hi
  rw [isoMap_hom_app_genSec e e (Iso.refl M) hT hT i i hi hi,
    isoUnit_self, one_smul]
  rfl

set_option maxHeartbeats 800000 in
/-- Determinant maps preserve composition as actual sheaf isomorphisms. -/
lemma isoMap_comp (φ : M ≅ N) (ψ : N ≅ P)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤)
    (hR : (⨆ k, R k) = ⊤) :
    isoMap e f φ hT hS ≪≫ isoMap f g ψ hS hR =
      isoMap e g (φ ≪≫ ψ) hT hR := by
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
  intro q W hW
  have hi : W ≤ T q.1 := hW.trans (inf_le_left.trans inf_le_left)
  have hj : W ≤ S q.2.1 := hW.trans (inf_le_left.trans inf_le_right)
  have hk : W ≤ R q.2.2 := hW.trans inf_le_right
  ext m
  obtain ⟨r, rfl⟩ := (CocycleGluing.smul_genSec_bijective
    (cocycle e) (isCocycle e) q.1 hi).2 m
  change (isoMap f g ψ hS hR).hom.app W
      ((isoMap e f φ hT hS).hom.app W
        (r • CocycleGluing.genSec (cocycle e) (isCocycle e) q.1 hi)) = _
  rw [Scheme.Modules.Hom.app_smul,
    isoMap_hom_app_genSec e f φ hT hS q.1 q.2.1 hi hj,
    Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul,
    isoMap_hom_app_genSec f g ψ hS hR q.2.1 q.2.2 hj hk,
    Scheme.Modules.Hom.app_smul,
    isoMap_hom_app_genSec e g (φ ≪≫ ψ) hT hR q.1 q.2.2 hi hk]
  simp only [smul_smul]
  rw [isoUnit_comp]

/-- The determinant map as an isomorphism of actual line bundles. -/
def lineBundleIsoMap (φ : M ≅ N)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) :
    lineBundle e hT ≅ lineBundle f hS :=
  ObjectProperty.isoMk _ (isoMap e f φ hT hS)

@[simp]
lemma lineBundleIsoMap_refl (hT : (⨆ i, T i) = ⊤) :
    lineBundleIsoMap e e (Iso.refl M) hT hT = Iso.refl _ := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (isoMap_refl e hT)

lemma lineBundleIsoMap_comp (φ : M ≅ N) (ψ : N ≅ P)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤)
    (hR : (⨆ k, R k) = ⊤) :
    lineBundleIsoMap e f φ hT hS ≪≫ lineBundleIsoMap f g ψ hS hR =
      lineBundleIsoMap e g (φ ≪≫ ψ) hT hR := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (isoMap_comp e f g φ ψ hT hS hR)

end Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames
