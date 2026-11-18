import Langlands.GroupScheme.RelativeUnipotent.FreeVectorBundle
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof
import Langlands.GroupScheme.VectorMatrixMap

/-! # Actual free-module maps from section images and matrices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.SchemeModule Langlands.Scheme.Modules
open scoped Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.FreeBundleMatrices

variable {S : Scheme.{u}}

/-- The actual global generator of the prescribed finite free sheaf. -/
def generator (S : Scheme.{u}) (n : ℕ) (i : Fin n) :
    GlobalSections (freeBundle S n) :=
  (SheafOfModules.freeSection (R := S.ringCatSheaf) (ULift.up i)).val (op ⊤)

/-- The actual free-module map with prescribed global section images. -/
def homOfSections (n : ℕ) (B : S.Modules) (v : Fin n → GlobalSections B) :
    freeBundle S n ⟶ B :=
  B.freeHomEquiv.symm (fun i : ULift.{u} (Fin n) => sectionFamily B (v i.down))

/-- The chosen actual generators have precisely the prescribed images. -/
lemma homOfSections_generator (n : ℕ) (B : S.Modules)
    (v : Fin n → GlobalSections B) (i : Fin n) :
    (homOfSections n B v).app ⊤ (generator S n i) = v i := by
  have H := congrArg (fun s => s.val (op ⊤))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (fun j : ULift.{u} (Fin n) => sectionFamily B (v j.down)) (ULift.up i))
  change (homOfSections n B v).app ⊤ (generator S n i) =
    B.presheaf.map (𝟙 (op ⊤)) (v i) at H
  simpa only [B.presheaf.map_id, ConcreteCategory.id_apply] using H

/-- Actual pullback of the prescribed map has the expected action on the
canonical pulled-back basis, on every scheme test. -/
lemma homOfSections_basis (n : ℕ) (B : S.Modules)
    (v : Fin n → GlobalSections B) (T : Over S) (i : Fin n) :
    ((Scheme.Modules.pullback T.hom).map (homOfSections n B v)).app ⊤
        (freeBundleBasis n T i) = pullbackSection T.hom B (v i) := by
  rw [freeBundleBasis_apply, ← pullbackSection_naturality]
  exact congrArg (pullbackSection T.hom B) (homOfSections_generator n B v i)

/-- The action on arbitrary finite free section coordinates. -/
lemma homOfSections_coordinates (n : ℕ) (B : S.Modules)
    (v : Fin n → GlobalSections B) (T : Over S) (x : Fin n → Γ(T.left, ⊤)) :
    ((Scheme.Modules.pullback T.hom).map (homOfSections n B v)).app ⊤
        (freeBundleSectionEquiv n T x) =
      ∑ i, x i • pullbackSection T.hom B (v i) := by
  rw [freeBundleSectionEquiv_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Scheme.Modules.Hom.app_smul, homOfSections_basis]

/-- The actual rectangular matrix map of finite free module sheaves. -/
def homOfMatrix {n m : ℕ} (M : Matrix (Fin m) (Fin n) Γ(S, ⊤)) :
    freeBundle S n ⟶ freeBundle S m :=
  homOfSections n (freeBundle S m) (fun i => ∑ j, M j i • generator S m j)

/-- Pullback of a linear combination of original generators has the actual
pulled-back coefficients in the canonical section basis. -/
lemma pullback_linearCombination (m : ℕ) (T : Over S) (v : Fin m → Γ(S, ⊤)) :
    pullbackSection T.hom (freeBundle S m) (∑ j, v j • generator S m j) =
      ∑ j, T.hom.appTop (v j) • freeBundleBasis m T j := by
  rw [pullbackSection_eq_sectionPullback, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smulₛₗ, freeBundleBasis_apply, pullbackSection_eq_sectionPullback]
  rfl

/-- Actual rectangular matrix sheaf maps act by the coefficient-pulled matrix
on all scheme-test section coordinates. -/
lemma homOfMatrix_coordinates {n m : ℕ}
    (M : Matrix (Fin m) (Fin n) Γ(S, ⊤)) (T : Over S)
    (x : Fin n → Γ(T.left, ⊤)) :
    ((Scheme.Modules.pullback T.hom).map (homOfMatrix M)).app ⊤
        (freeBundleSectionEquiv n T x) =
      freeBundleSectionEquiv m T ((M.map T.hom.appTop.hom) *ᵥ x) := by
  classical
  rw [homOfMatrix, homOfSections_coordinates, freeBundleSectionEquiv_apply]
  simp_rw [pullback_linearCombination, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-- A compatible global section family is determined by its value at the top open. -/
lemma sections_ext_top {B : S.Modules} (s t : B.sections)
    (h : s.val (op ⊤) = t.val (op ⊤)) : s = t := by
  apply PresheafOfModules.sections_ext
  intro U
  rw [← s.property (homOfLE (show U.unop ≤ ⊤ from le_top)).op,
    ← t.property (homOfLE (show U.unop ≤ ⊤ from le_top)).op, h]

/-- The actual global free generators detect equality of actual module-sheaf maps. -/
lemma hom_ext {n : ℕ} {B : S.Modules} (f g : freeBundle S n ⟶ B)
    (h : ∀ i, f.app ⊤ (generator S n i) = g.app ⊤ (generator S n i)) : f = g := by
  apply B.freeHomEquiv.injective
  funext i
  rcases i with ⟨i⟩
  apply sections_ext_top
  exact h i

/-- The actual global generator formula for a rectangular matrix map. -/
lemma homOfMatrix_generator {n m : ℕ} (M : Matrix (Fin m) (Fin n) Γ(S, ⊤)) (i : Fin n) :
    (homOfMatrix M).app ⊤ (generator S n i) =
      ∑ j, M j i • generator S m j :=
  homOfSections_generator n _ _ i

/-- Composition of actual free-sheaf maps is multiplication of the prescribed matrices. -/
lemma homOfMatrix_comp {n m l : ℕ} (M : Matrix (Fin m) (Fin n) Γ(S, ⊤))
    (N : Matrix (Fin l) (Fin m) Γ(S, ⊤)) :
    homOfMatrix M ≫ homOfMatrix N = homOfMatrix (N * M) := by
  classical
  apply hom_ext
  intro i
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    homOfMatrix_generator, homOfMatrix_generator, map_sum]
  simp_rw [Scheme.Modules.Hom.app_smul, homOfMatrix_generator, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.mul_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

/-- The identity matrix gives the identity map of the actual free sheaf. -/
lemma homOfMatrix_one (n : ℕ) :
    homOfMatrix (1 : Matrix (Fin n) (Fin n) Γ(S, ⊤)) = 𝟙 (freeBundle S n) := by
  classical
  apply hom_ext
  intro i
  rw [homOfMatrix_generator]
  simp [Matrix.one_apply]

/-- Inverse rectangular matrices give an actual isomorphism of the free sheaves. -/
def isoOfMatrices {n m : ℕ}
    (M : Matrix (Fin m) (Fin n) Γ(S, ⊤))
    (N : Matrix (Fin n) (Fin m) Γ(S, ⊤))
    (hNM : N * M = 1) (hMN : M * N = 1) :
    freeBundle S n ≅ freeBundle S m where
  hom := homOfMatrix M
  inv := homOfMatrix N
  hom_inv_id := by rw [homOfMatrix_comp, hNM, homOfMatrix_one]
  inv_hom_id := by rw [homOfMatrix_comp, hMN, homOfMatrix_one]

/-- The actual polynomial vector-group matrix map and the actual module-sheaf
matrix map have the same canonical section coordinates on every scheme test. -/
lemma vectorGroup_matrixHom_sections {R : CommRingCat.{u}} {n m : ℕ}
    (M : Matrix (Fin m) (Fin n) R) (T : Over (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R n).X) :
    (freeVectorBundlePoints R m T (x ≫ (VectorGroup.matrixHom M).hom.hom)).toAdd =
      ((Scheme.Modules.pullback T.hom).map
        (homOfMatrix (M.map (Scheme.ΓSpecIso R).inv.hom))).app ⊤
          (freeVectorBundlePoints R n T x).toAdd := by
  change freeBundleSectionEquiv m T
      (VectorGroup.coordinates R m T (x ≫ (VectorGroup.matrixHom M).hom.hom)).toAdd =
    ((Scheme.Modules.pullback T.hom).map
      (homOfMatrix (M.map (Scheme.ΓSpecIso R).inv.hom))).app ⊤
        (freeBundleSectionEquiv n T (VectorGroup.coordinates R n T x).toAdd)
  rw [VectorGroup.coordinates_matrixHom, homOfMatrix_coordinates]
  rfl

end Langlands.GroupScheme.RelativeUnipotent.FreeBundleMatrices
