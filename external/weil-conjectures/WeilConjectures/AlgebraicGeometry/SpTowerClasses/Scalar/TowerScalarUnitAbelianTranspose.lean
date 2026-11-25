/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerRestrictedScalarAdjunction
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarUnitAbelianTransposeSection

/-! # The abelian transpose of the coefficient-unit comparison

Source: blueprint classes proof (2), ordinary coefficient-unit normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The coefficient-unit normalization after forgetting and taking abelian adjuncts.
There is no scalar-association map or adjunction for d.pull in this assertion.

Source: blueprint latest, classes proof (2), unit normalization in ordinary
coefficient extension; Stacks 03EL.
(blueprint: lem-sp-tower-scalar-unit-abelian-transpose).

Proof: evaluate both tower maps at n. The ordinary scalar adjunction unit sends
x to 1 tensor x. Thus the assumptions on eY and eX identify their transposes
with the quotient ring map on every section. The naturality of the ordinary
geometric adjunction moves eY outside the transpose. Through the section
normalization of chi, the transpose of theta0 is the constant-ring restriction
in CoefficientPullback.normalization. On constant integer sections both sides
are therefore the same unital quotient map, by d.unit_normalization and the
definition of integerPull. Locally a section of Rlevel lifts to a constant
integer; the sheafification unit of the constant presheaf is locally surjective.
Linearity and separatedness extend the equality from those integer sections
to all sections. The section, restriction and morphism equations of Forget
identify this equality with the displayed abelian tower equality. Ordinary
evaluations are jointly faithful, so equality at every level proves the result.
No derived normalization or flatness enters; zero rings and empty charts are
included by the same separatedness argument. -/
theorem scalarUnit_abelianTranspose
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (d : IntegralCoefficientPullback l E f cY cX)
    (χ : (g.push ⋙ SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E Y)) ⋙ cY.reduction.forget.F ≅
      (SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E X) ⋙ cX.reduction.forget.F) ⋙ abPush f)
    (hχ : ∀ (N : Systems X (Arings l E X)) (n : ℕ) (U : Y.ProEtᵒᵖ)
      (x : (((cY.reduction.forget.F.obj
        ((SemilinearSections.res.{u + 1, u, u + 1}
          (coefficientSystemMap l E Y)).obj (g.push.obj N))).obj (op n)).obj.obj U)),
      HEq ((((χ.hom.app N).app (op n)).hom.app U) x) x)
    (θ₀ : CoefficientPullback l E b f g)
    (eY : cY.scalar.model.E.obj (coefficient Y (Rrings l Y)) ⟶
      coefficient Y (Arings l E Y))
    (eX : cX.scalar.model.E.obj (coefficient X (Rrings l X)) ⟶
      coefficient X (Arings l E X))
    (heY : (cY.scalar.ordinaryAdjunction.homEquiv _ _) eY = scalarGenerator l E Y)
    (heX : (cX.scalar.ordinaryAdjunction.homEquiv _ _) eX = scalarGenerator l E X) :
    cY.reduction.forget.F.map
        (((cY.scalar.ordinaryAdjunction.comp g.ordinaryAdjunction).homEquiv _ _)
          (g.pull.map eY ≫ θ₀.iso.hom)) ≫
        χ.hom.app (coefficient X (Arings l E X)) =
      ((abAdjunction f).homEquiv _ _)
        (d.forgetIso.hom.app (coefficient Y (Rrings l Y)) ≫
          cX.reduction.forget.F.map
            ((cX.scalar.ordinaryAdjunction.homEquiv _ _)
              (cX.scalar.model.E.map d.unitIso.hom ≫ eX))) := by
  apply NatTrans.ext
  funext n
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact scalarUnit_abelianTranspose_section l E f b g cY cX d χ hχ θ₀ eY eX heY heX n U x

end AlgebraicGeometry.ProEtale.SpTowerClasses
