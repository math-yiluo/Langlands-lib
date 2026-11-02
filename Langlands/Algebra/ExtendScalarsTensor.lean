import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic

/-! # Scalar extension and the algebra tensor product -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory
open scoped ChangeOfRings TensorProduct

namespace Langlands.Scheme.Modules

variable (A B : CommRingCat.{u}) [Algebra A B]

/-- The additive map `B ⊗[A, algebraMap A B] M → B ⊗[A] M`, `b ⊗ₜ m ↦ b ⊗ₜ m`. -/
def extendScalarsToAlgebraTensor (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj M →+ B ⊗[A] M :=
  TensorProduct.liftAddHom (R := A)
    (M := (ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj
      (ModuleCat.of B B)) (N := M)
    (AddMonoidHom.mk' (fun b => (TensorProduct.mk A B M b).toAddMonoidHom)
      (fun b c => by ext m; exact TensorProduct.add_tmul (R := A) (M := B) b c m))
    (fun a b m => by
      change (algebraMap A B a * (show B from b)) ⊗ₜ[A] m = (show B from b) ⊗ₜ[A] (a • m)
      rw [← Algebra.smul_def, TensorProduct.smul_tmul])

/-- The additive map `B ⊗[A] M → B ⊗[A, algebraMap A B] M`, `b ⊗ₜ m ↦ b ⊗ₜ m`. -/
def algebraTensorToExtendScalars (M : ModuleCat.{u} A) :
    B ⊗[A] M →+ (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj M :=
  TensorProduct.liftAddHom (R := A) (M := B) (N := M)
    (AddMonoidHom.mk'
      (fun b => (TensorProduct.mk A
        ((ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj
          (ModuleCat.of B B)) M b).toAddMonoidHom)
      (fun b c => by
        ext m
        exact TensorProduct.add_tmul (R := A)
          (M := (ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj
            (ModuleCat.of B B)) b c m))
    (fun a b m => by
      rw [Algebra.smul_def]
      exact TensorProduct.smul_tmul (R := A)
        (M := (ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj
          (ModuleCat.of B B)) (N := M) a b m)

/-- For an `A`-algebra `B`, scalar extension along `algebraMap A B` is the algebra tensor product
`B ⊗[A] M`. The two `A`-module structures on `B` (through `algebraMap A B`, and the algebra
structure) agree only propositionally, so this is a `B`-linear equivalence rather than an
equality of modules. -/
def extendScalarsAlgebraEquiv (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj M ≃ₗ[B] B ⊗[A] M where
  toFun := extendScalarsToAlgebraTensor A B M
  invFun := algebraTensorToExtendScalars A B M
  map_add' := map_add _
  map_smul' b' x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  left_inv x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  right_inv x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The `B`-linear isomorphism `B ⊗[A, algebraMap A B] M ≅ B ⊗[A] M` in `ModuleCat B`. -/
def extendScalarsAlgebraIso (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj M ≅
      ModuleCat.of B (B ⊗[A] M) :=
  (extendScalarsAlgebraEquiv A B M).toModuleIso

lemma extendScalarsAlgebraIso_hom_tmul (M : ModuleCat.{u} A) (b : B) (m : M) :
    (extendScalarsAlgebraIso A B M).hom (b ⊗ₜ[A, (CommRingCat.ofHom (algebraMap A B)).hom] m) =
      b ⊗ₜ[A] m :=
  rfl

end Langlands.Scheme.Modules
