/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import all WeilConjectures.CategoryTheory.Exact.ExactDerivedTensorSquare
import all WeilConjectures.CategoryTheory.ZetaWeil.RestrictedTransportBraiding

/-! # Monoidal squares of coefficient-normalized module inverse images -/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
namespace CategoryTheory
set_option autoImplicit false
set_option synthInstance.maxSize 4096

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [SymmetricCategory D]
  [HasCoequalizers D]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
  {A : C} [MonObj A] [IsCommMonObj A] {B : D} [MonObj B] [IsCommMonObj B]
  (a : B ⟶ F.obj A) [IsMonHom a] [IsIso a]

variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [SymmetricCategory E]
  [HasCoequalizers E]
  [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {T : Type u₄} [Category.{v₄} T] [MonoidalCategory T] [SymmetricCategory T]
  [HasCoequalizers T]
  [∀ X : T, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : T, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (G : D ⥤ T) (H : C ⥤ E) (I : E ⥤ T)
  [G.Braided] [H.Braided] [I.Braided]
  [PreservesColimitsOfShape WalkingParallelPair G]
  [PreservesColimitsOfShape WalkingParallelPair H]
  [PreservesColimitsOfShape WalkingParallelPair I]
  {R : E} [MonObj R] [IsCommMonObj R] {S : T} [MonObj S] [IsCommMonObj S]
  (b : S ⟶ G.obj B) [IsMonHom b] [IsIso b]
  (c : R ⟶ H.obj A) [IsMonHom c] [IsIso c]
  (d : S ⟶ I.obj R) [IsMonHom d] [IsIso d]

end CategoryTheory
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
namespace CategoryTheory
set_option autoImplicit false
set_option synthInstance.maxSize 4096

end CategoryTheory
