/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerRestrictedScalarAdjunction
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarUnitAbelianTransposeSectionNormalized

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

/-! # Sectionwise coefficient-unit transpose

This module isolates the section calculation used by the abelian transpose theorem.
-/

/-- Sectionwise form of the coefficient-unit transpose.

Source: blueprint classes proof (2), ordinary coefficient-unit normalization;
Stacks 03EL.  This is the sectionwise calculation underlying
`scalarUnit_abelianTranspose` (blueprint: lem-sp-tower-scalar-unit-abelian-transpose).
The remaining theorem only assembles these equalities by extensionality.

Proof: evaluate the two ordinary adjuncts on a fixed level and chart. The equations
heY and heX replace both scalar adjuncts by scalarGenerator. Adjunction naturality
moves eY through the geometric transpose, while hχ identifies the section comparison
with the identity. CoefficientPullback.normalization and d.unit_normalization then
identify both resulting maps on constant integer generators with integerPull. The
constant integer sheaf is locally surjective, so additivity and separatedness extend
the equality to every section. This works on empty charts and zero rings as well.
-/
theorem scalarUnit_abelianTranspose_section
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
    (heX : (cX.scalar.ordinaryAdjunction.homEquiv _ _) eX = scalarGenerator l E X)
    (n : ℕᵒᵖ) (U : Y.ProEtᵒᵖ)
    (x : ((cY.reduction.forget.F.obj (coefficient Y (Rrings l Y))).obj n).obj.obj U) :
    (AddCommGrpCat.Hom.hom
      (((cY.reduction.forget.F.map
        (((cY.scalar.ordinaryAdjunction.comp g.ordinaryAdjunction).homEquiv _ _)
          (g.pull.map eY ≫ θ₀.iso.hom)) ≫
        χ.hom.app (coefficient X (Arings l E X))).app n).hom.app U)) x =
      (AddCommGrpCat.Hom.hom
        (((((abAdjunction f).homEquiv _ _)
          (d.forgetIso.hom.app (coefficient Y (Rrings l Y)) ≫
            cX.reduction.forget.F.map
              ((cX.scalar.ordinaryAdjunction.homEquiv _ _)
                (cX.scalar.model.E.map d.unitIso.hom ≫ eX)))).app n).hom.app U)) x := by
  have hY : eY = canonicalScalarUnit l E cY := by
    apply (cY.scalar.ordinaryAdjunction.homEquiv _ _).injective
    simpa only [canonicalScalarUnit, Equiv.apply_symm_apply] using heY
  have hX : eX = canonicalScalarUnit l E cX := by
    apply (cX.scalar.ordinaryAdjunction.homEquiv _ _).injective
    simpa only [canonicalScalarUnit, Equiv.apply_symm_apply] using heX
  subst eY
  subst eX
  exact scalarUnit_abelianTranspose_section_normalized l E f b g cY cX d χ hχ θ₀ n U x

end AlgebraicGeometry.ProEtale.SpTowerClasses
