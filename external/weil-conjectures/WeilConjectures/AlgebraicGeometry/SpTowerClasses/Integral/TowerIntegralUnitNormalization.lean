/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryInverseSystem
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralUnitNormalizationComponents

/-! # Unit normalization for integral ordinary inverse systems

Source: blueprint classes proof (2), integral reduction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- The coefficient unit comparison is normalized on constant integer sections.
Source: blueprint latest, classes proof (2), integral reduction, and the defining
properties of `integerGenerator` and `integerPull`.
(blueprint: lem-sp-tower-integral-unit-normalization).

Proof: apply the ringUnderlying comparison to the coefficient module.  The ring
addition, multiplication, zero and one equations, together with module scalar
compatibility, make it a linear isomorphism and the ordinary transition equation
assembles it over the tower.  On constant integer sections the composite sends
one to one and preserves addition, hence it fixes every integer.  The universal
property defining `integerGenerator`, the adjunction defining `integerPull`, and
sheafification of constant sections then give the displayed equality.
-/
theorem integralInverseSystem_unit_normalization (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      ((Rrings l Y).obj (Opposite.op n)) ((Rrings l X).obj (Opposite.op n)))
    (P : WeilConjectures.SemilinearSections.OrdinaryInverseSystem.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
      (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)
      (Scheme.ProEt.topology X) (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (fun n ↦ (Rrings l X).obj (Opposite.op n))
      (fun n ↦ (Rrings l X).map (homOfLE (Nat.le_succ n)).op) I)
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X))
    (e : FY.F ⋙ abPull f ≅ P.pull ⋙ FX.F) :
    ∃ i : P.pull.obj (coefficient Y (Rrings l Y)) ≅ coefficient X (Rrings l X),
      (abPull f).map (integerGenerator Y (Rrings l Y) FY) ≫
          e.hom.app (coefficient Y (Rrings l Y)) ≫ FX.F.map i.hom =
        integerPull f ≫ integerGenerator X (Rrings l X) FX := by
  obtain ⟨i, hi⟩ := integralInverseSystem_unit_normalization_components l f I P FY FX e
  refine ⟨i, ?_⟩
  apply NatTrans.ext
  funext n
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact hi n.unop U x

end AlgebraicGeometry.ProEtale.SpTowerClasses
