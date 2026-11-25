/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralClassPullback
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryInverseSystem
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralAbelianComparison
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralUnitNormalization

/-! # Normalization of integral ordinary inverse systems

Source: blueprint classes proof (2), integral reduction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- The ordinary inverse-system construction has its underlying abelian and unit comparisons.
Source: blueprint latest, classes proof (2), integral reduction, and Zheng Construction 4.1.
(blueprint: lem-sp-tower-integral-inverse-system-normalization).

Proof: at each level, the moduleUnderlying comparison of I identifies the underlying set
sheaf with inverse image. Its moduleAdd and moduleZero graph equations lift this to the
abelian inverse image. Compose with the component comparison of P and the evaluation
identifications supplied by each Forget. Naturality in module morphisms gives naturality
in the system. The transition equation of P and restriction_underlying identify the two
horizontal arrows, so these level comparisons assemble into a whole-tower isomorphism e.
The coefficient module is the ring with its multiplication action. The ringUnderlying
comparison, with ringAdd, ringMul, ringZero and ringOne, identifies its inverse image with
the coefficient module on X; moduleSMul makes this identification linear. The same
transition equation assembles it into i. On constant integer sections the composite of
e and i sends z to z: ringOne handles 1, ringAdd and ringZero handle all integers. The
adjunction defining integerPull and the section formula defining integerGenerator then
give the displayed normalization. Sheafification extends these identities from constant
sections, which locally generate the constant integral quotient sheaves. No geometric
invertibility assumption or Chern datum is needed for these comparisons. -/
theorem integralInverseSystem_normalization (l : ℕ) [Fact l.Prime]
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
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X)) :
    ∃ e : FY.F ⋙ abPull f ≅ P.pull ⋙ FX.F,
      ∃ i : P.pull.obj (coefficient Y (Rrings l Y)) ≅ coefficient X (Rrings l X),
        (abPull f).map (integerGenerator Y (Rrings l Y) FY) ≫
          e.hom.app (coefficient Y (Rrings l Y)) ≫ FX.F.map i.hom =
        integerPull f ≫ integerGenerator X (Rrings l X) FX := by
  obtain ⟨e⟩ := integralInverseSystem_abelian_comparison l f I P FY FX
  obtain ⟨i, hi⟩ := integralInverseSystem_unit_normalization l f I P FY FX e
  exact ⟨e, i, hi⟩

end AlgebraicGeometry.ProEtale.SpTowerClasses
