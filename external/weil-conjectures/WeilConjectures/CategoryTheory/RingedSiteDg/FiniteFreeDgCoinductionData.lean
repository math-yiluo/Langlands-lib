/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDg.SheafDgHomotopySystem

/-! Shared data records for finite-free sheaf DG coinduction.

(blueprint: def-sf-finite-free-dg-coinduction-data-stage3) -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}

-- Elaborating the comparison evaluation uses the same budget as the full record.
/-- The ordinary coinduction and tensor-dual data, without free extension.
Source: Stacks 0FRS (blueprint: lem-sf-finite-free-dg-coinduction-ordinary-core-stage3). -/
structure FiniteFreeCoinductionOrdinaryCore (A : Algebra O) where
  coinduction : Complex O ⥤ Module A
  evaluation (M : Complex O) : (underlying A).obj (coinduction.obj M) ⊗ A.X ⟶ M
  hom_universal (M L : Complex O) : Function.Bijective
    (fun f : L ⟶ (underlying A).obj (coinduction.obj M) ↦
      (f ▷ A.X) ≫ evaluation M)
  evaluation_natural {M N : Complex O} (f : M ⟶ N) :
    ((underlying A).map (coinduction.map f) ▷ A.X) ≫ evaluation N = evaluation M ≫ f
  hom_action (M : Complex O) :
    (action (coinduction.obj M) ▷ A.X) ≫ evaluation M =
      (α_ ((underlying A).obj (coinduction.obj M)) A.X A.X).hom ≫
        (((underlying A).obj (coinduction.obj M)) ◁
          (MonObj.mul : A.X ⊗ A.X ⟶ A.X)) ≫ evaluation M
  tensorDual : Complex O ⥤ Module A
  tensorDualIso : tensorDual ⋙ underlying A ≅
    tensorRight ((underlying A).obj (coinduction.obj (𝟙_ (Complex O))))
  tensorDual_action (M : Complex O) :
    action (tensorDual.obj M) ≫ tensorDualIso.hom.app M =
      (tensorDualIso.hom.app M ▷ A.X) ≫
        (α_ M ((underlying A).obj (coinduction.obj (𝟙_ (Complex O)))) A.X).hom ≫
        (M ◁ action (coinduction.obj (𝟙_ (Complex O))))
  comparison : tensorDual ≅ coinduction
  comparison_evaluation (M : Complex O) :
    ((underlying A).map (comparison.hom.app M) ▷ A.X) ≫ evaluation M =
      (tensorDualIso.hom.app M ▷ A.X) ≫
        (α_ M ((underlying A).obj (coinduction.obj (𝟙_ (Complex O)))) A.X).hom ≫
        (M ◁ evaluation (𝟙_ (Complex O))) ≫ (ρ_ M).hom

end CategoryTheory.RingedSiteDg
