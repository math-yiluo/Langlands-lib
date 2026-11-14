import Langlands.AlgebraicGeometry.Picard.DeterminantCoverChange

/-! # Determinant lines and actual module-sheaf isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.DeterminantFrames

open Langlands.Scheme.Modules

variable {X : Scheme.{u}} {M N P : X.Modules} {ι κ μ I : Type u}
  [Fintype I] {T : ι → X.Opens} {S : κ → X.Opens} {R : μ → X.Opens}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i)) I ≅ M.over (T i))
  (f : ∀ j, SheafOfModules.free (R := X.ringCatSheaf.over (S j)) I ≅ N.over (S j))
  (g : ∀ k, SheafOfModules.free (R := X.ringCatSheaf.over (R k)) I ≅ P.over (R k))

local instance : DecidableEq I := Classical.decEq I

/-- The actual linear equivalence induced on sections by a sheaf isomorphism. -/
def sectionLinearEquiv (φ : M ≅ N) (V : X.Opens) :
    Γ(M, V) ≃ₗ[Γ(X, V)] Γ(N, V) where
  toFun := φ.hom.app V
  invFun := φ.inv.app V
  left_inv x := by
    change (φ.hom ≫ φ.inv).app V x = x
    rw [φ.hom_inv_id]
    rfl
  right_inv x := by
    change (φ.inv ≫ φ.hom).app V x = x
    rw [φ.inv_hom_id]
    rfl
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul φ.hom

/-- Transport the actual frame isomorphisms along a module-sheaf isomorphism. -/
def mapFrames (φ : M ≅ N) (i : ι) :
    SheafOfModules.free (R := X.ringCatSheaf.over (T i)) I ≅ N.over (T i) :=
  e i ≪≫ (SheafOfModules.overFunctor X.ringCatSheaf (T i)).mapIso φ

lemma basis_mapFrames (φ : M ≅ N) (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    basis (mapFrames e φ) i hi = (basis e i hi).map (sectionLinearEquiv φ V) := by
  ext a
  change localSectionBasis (mapFrames e φ i) (Over.mk (homOfLE hi)) a =
    (sectionLinearEquiv φ V) (localSectionBasis (e i) (Over.mk (homOfLE hi)) a)
  calc
    _ = (localBasisSection (mapFrames e φ i) a).val
        (op (Over.mk (homOfLE hi))) :=
      localSectionBasis_apply (mapFrames e φ i) (Over.mk (homOfLE hi)) a
    _ = (sectionLinearEquiv φ V)
        ((localBasisSection (e i) a).val (op (Over.mk (homOfLE hi)))) :=
      congrArg (fun s => s.val (op (Over.mk (homOfLE hi))))
        (SheafOfModules.freeHomEquiv_comp_apply (e i).hom
          ((SheafOfModules.overFunctor X.ringCatSheaf (T i)).map φ.hom) a)
    _ = _ := congrArg (sectionLinearEquiv φ V)
      (localSectionBasis_apply (e i) (Over.mk (homOfLE hi)) a).symm

lemma matrix_mapFrames (φ : M ≅ N) (i j : ι) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ T j) :
    matrix (mapFrames e φ) i j hi hj = matrix e i j hi hj := by
  unfold matrix
  rw [basis_mapFrames, basis_mapFrames, Module.Basis.toMatrix_map]
  ext a b
  simp only [Module.Basis.toMatrix_apply, Function.comp_apply, Module.Basis.map_apply,
    LinearEquiv.symm_apply_apply]

/-- Transporting every frame preserves the actual determinant cocycle. -/
lemma cocycle_mapFrames (φ : M ≅ N) : cocycle (mapFrames e φ) = cocycle e := by
  funext i j
  apply Units.ext
  exact congrArg Matrix.det (matrix_mapFrames e φ i j inf_le_left inf_le_right)

/-- Equality transport between glued cocycles preserves their local generators. -/
lemma eqToIso_hom_app_genSec
    {c d : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ} (h : c = d)
    (hc : CocycleGluing.IsCocycle c) (hd : CocycleGluing.IsCocycle d)
    (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    (eqToIso (congrArg CocycleGluing.glued h)).hom.app V
        (CocycleGluing.genSec c hc i hi) =
      CocycleGluing.genSec d hd i hi := by
  cases h
  rfl

/-- The determinant comparison to the transported frame system. -/
def mapFramesIso (φ : M ≅ N) :
    CocycleGluing.glued (cocycle e) ≅ CocycleGluing.glued (cocycle (mapFrames e φ)) :=
  eqToIso (congrArg CocycleGluing.glued (cocycle_mapFrames e φ).symm)

lemma mapFramesIso_hom_app_genSec (φ : M ≅ N)
    (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    (mapFramesIso e φ).hom.app V (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi) =
      CocycleGluing.genSec (cocycle (mapFrames e φ)) (isCocycle (mapFrames e φ)) i hi :=
  eqToIso_hom_app_genSec (cocycle_mapFrames e φ).symm _ _ i hi

/-- The coordinate matrix of the actual sheaf isomorphism in the two frames. -/
def isoMatrix (φ : M ≅ N) (i : ι) (j : κ) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ S j) : Matrix I I Γ(X, V) :=
  LinearMap.toMatrix (basis e i hi) (basis f j hj) (φ.hom.val.app (op V)).hom

lemma isoMatrix_comp (φ : M ≅ N) (ψ : N ≅ P)
    (i : ι) (j : κ) (k : μ) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ S j) (hk : V ≤ R k) :
    isoMatrix f g ψ j k hj hk * isoMatrix e f φ i j hi hj =
      isoMatrix e g (φ ≪≫ ψ) i k hi hk := by
  rw [isoMatrix, isoMatrix, isoMatrix, ← LinearMap.toMatrix_comp]
  rfl

/-- The determinant of the actual isomorphism in the supplied frames. -/
def isoUnit (φ : M ≅ N) (i : ι) (j : κ) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ S j) : (Γ(X, V))ˣ :=
  coverChangeUnit (mapFrames e φ) f i j hi hj

lemma isoUnit_val (φ : M ≅ N) (i : ι) (j : κ) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ S j) :
    (isoUnit e f φ i j hi hj : Γ(X, V)) = (isoMatrix e f φ i j hi hj).det := by
  change ((basis f j hj).toMatrix (basis (mapFrames e φ) i hi)).det = _
  congr 1
  ext a b
  simp only [Module.Basis.toMatrix_apply, isoMatrix, LinearMap.toMatrix_apply,
    basis_mapFrames, Module.Basis.map_apply]
  rfl

lemma isoUnit_self (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    (isoUnit e e (Iso.refl M) i i hi hi : Γ(X, V)) = 1 := by
  rw [isoUnit_val]
  change (LinearMap.toMatrix (basis e i hi) (basis e i hi) LinearMap.id).det = 1
  rw [LinearMap.toMatrix_id, Matrix.det_one]

lemma isoUnit_comp (φ : M ≅ N) (ψ : N ≅ P)
    (i : ι) (j : κ) (k : μ) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ S j) (hk : V ≤ R k) :
    (isoUnit e f φ i j hi hj : Γ(X, V)) *
        (isoUnit f g ψ j k hj hk : Γ(X, V)) =
      (isoUnit e g (φ ≪≫ ψ) i k hi hk : Γ(X, V)) := by
  rw [isoUnit_val, isoUnit_val, isoUnit_val, mul_comm, ← Matrix.det_mul, isoMatrix_comp]

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

end Langlands.AlgebraicGeometry.Picard.DeterminantFrames
