/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerRestrictedScalarAdjunction
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarRootAbelianTransposeCore

/-! # Finite-level component of the scalar root abelian transpose -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite-level component calculation underlying the scalar root transpose.

Source: blueprint latest, classes proof (2), Kummer roots followed by ordinary
coefficient extension; Stacks 03EL.
(blueprint: lem-sp-tower-scalar-root-abelian-transpose-component)

Proof: evaluate the two displayed tower morphisms at one finite level and one
pro-etale chart. The Kummer root restriction, the normalized line evaluation,
and the section identity of chi give the same value on every section. This is
the component form of the first Kummer square and the ordinary scalar unit
calculation; the remaining assembly over levels is handled by the parent
transpose theorem.
-/
theorem scalarRoot_abelianTranspose_component
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
    (hk : ∀ n : ℕ, d.kummer.τ₂.app (op n) = (unitsPull f).app (op n))
    (θ₁ : LinePullback l E f g cY cX)
    (n : ℕᵒᵖ) (U : Y.ProEtᵒᵖ)
    (x : (((cY.reduction.forget.F.obj cY.rootModule).obj n).obj.obj U)) :
    (((cY.reduction.forget.F.map
        (((cY.scalar.ordinaryAdjunction.comp g.ordinaryAdjunction).homEquiv _ _)
          θ₁.iso.hom) ≫ χ.hom.app (lineModule l E cX)).app n).hom.app U) x =
      (((((abAdjunction f).homEquiv _ _)
        (d.forgetIso.hom.app cY.rootModule ≫ cX.reduction.forget.F.map
          ((cX.scalar.ordinaryAdjunction.homEquiv _ _)
            (cX.scalar.model.E.map d.rootIso.hom)))).app n).hom.app U) x := by
  simp only [Adjunction.comp_homEquiv]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  let w := scalarRootCoreSource l E f b g cY cX θ₁ n U x
  have hw := hχ (lineModule l E cX) n.unop U w
  have hcore := scalarRoot_abelianTranspose_core l E f b g cY cX d hk θ₁ n U x
  apply eq_of_heq
  exact hw.trans (by
    simpa only [w, scalarRootCoreRight, Adjunction.homEquiv_unit,
      Functor.map_comp] using hcore)

end AlgebraicGeometry.ProEtale.SpTowerClasses
