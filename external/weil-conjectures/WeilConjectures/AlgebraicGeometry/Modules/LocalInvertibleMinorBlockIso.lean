/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
universe u
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- A square map of finite free sheaves with unit determinant is invertible. -/
theorem local_invertible_minor_block_isIso
    {X : Scheme.{u}} {I : Type u} [Fintype I] [DecidableEq I]
    (f : free (R := X.ringCatSheaf) I ⟶ free I)
    (hdet : IsUnit (freeMatrix f).det) : IsIso f := by
  classical
  let S (M : X.Modules) : M.sections ≃ Γ(M, ⊤) :=
    { toFun := fun s ↦ s.val (.op ⊤)
      invFun := fun x ↦ M.val.sectionsMk
        (fun V ↦ M.val.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op x)
        (fun V W k ↦ by
          rw [← M.val.map_comp_apply]
          congr 1)
      left_inv := fun s ↦ by
        apply PresheafOfModules.sections_ext
        intro V
        exact PresheafOfModules.sections_property s _
      right_inv := fun x ↦ by
        change M.val.map (𝟙 _) x = x
        simp }
  let E : (free (R := X.ringCatSheaf) I ⟶ free I) ≃
      (I → Γ(free (R := X.ringCatSheaf) I, ⊤)) :=
    (free (R := X.ringCatSheaf) I).freeHomEquiv.trans
      (Equiv.piCongrRight fun _ ↦ S (free (R := X.ringCatSheaf) I))
  have hmatrix (p : free (R := X.ringCatSheaf) I ⟶ free I) (i k : I) :
      freeMatrix p k i = freeSectionsEquiv I (E p i) k := rfl
  have hinj : Function.Injective
      (freeMatrix (X := X) (I := I) (J := I)) := by
    intro p q hpq
    apply E.injective
    funext i
    apply (freeSectionsEquiv I).injective
    funext k
    exact congrArg (fun A ↦ A k i) hpq
  have hcomp (p q : free (R := X.ringCatSheaf) I ⟶ free I) :
      freeMatrix (p ≫ q) = freeMatrix q * freeMatrix p := by
    ext k i
    rw [hmatrix]
    change freeSectionsEquiv I (Hom.app q ⊤ (E p i)) k = _
    rw [freeSectionsEquiv_app]
    rfl
  have hid : freeMatrix (𝟙 (free (R := X.ringCatSheaf) I)) = 1 := by
    ext k i
    simp [freeMatrix, freeπ_app_ιFree_app, Matrix.one_apply, eq_comm]
  let B := (freeMatrix f)⁻¹
  let g : free (R := X.ringCatSheaf) I ⟶ free I :=
    E.symm (fun i ↦ (freeSectionsEquiv I).symm (fun k ↦ B k i))
  have hg : freeMatrix g = B := by
    ext k i
    rw [hmatrix]
    simp [g]
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply hinj
    rw [hcomp, hg, hid]
    exact Matrix.nonsing_inv_mul _ hdet
  · apply hinj
    rw [hcomp, hg, hid]
    exact Matrix.mul_nonsing_inv _ hdet

end AlgebraicGeometry.Scheme.Modules
