/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernPullbackData
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarUnitAbelianTranspose
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarRootAbelianTranspose

/-! # Ordinary scalar association for a fixed integral geometric inverse image

Source: blueprint classes proof (2), balanced coefficient extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w x
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

private theorem forget_map_injective (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) {M N : Systems T B} {a b : M ⟶ N}
    (h : F.F.map a = F.F.map b) : a = b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h' := congrArg (fun t : F.F.obj M ⟶ F.F.obj N ↦
    (((t.app (Opposite.op W.unop.1)).hom.app (Opposite.op W.unop.2)).hom)) h
  have hh := (F.morphisms a W.unop.1 (Opposite.op W.unop.2)).symm.trans
    (h'.heq.trans (F.morphisms b W.unop.1 (Opposite.op W.unop.2)))
  exact DFunLike.congr_fun (eq_of_heq hh) x

private theorem comparison_transpose
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{x} D]
    {F G : C ⥤ D} {H : D ⥤ C} (a : F ⊣ H) (b : G ⊣ H)
    (M : C) (N : D) (t : G.obj M ⟶ N) :
    (a.homEquiv M N) ((a.leftAdjointUniq b).hom.app M ≫ t) =
      (b.homEquiv M N) t := by
  rw [a.homEquiv_naturality_right, a.homEquiv_leftAdjointUniq_hom_app,
    b.homEquiv_unit]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Balanced scalar association for already constructed integral inverse image.
The coefficient arrows are specified by their ordinary adjuncts; no derived
counit or K-flatness condition occurs in the statement.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
ordinary coefficient extension; balanced association of scalar extension
(Stacks 03EL).
(blueprint: lem-sp-tower-ordinary-scalar-association).

Proof: restrictedScalarAdjunction_exists gives the normalized adjunction from
integral inverse image followed by ordinary scalar extension to geometric direct
image followed by coefficient restriction. The source scalar adjunction composed
with the geometric adjunction has this same right adjoint. Uniqueness of left
adjoints gives alpha. The Hom equivalence of the first adjunction sends
alpha_M followed by t to the Hom equivalence of the second adjunction applied
to t; this follows from the unit equation for leftAdjointUniq and naturality.
The recorded Forget functor is faithful: its morphism equation identifies every
component with the underlying additive component of the original module map.
To prove either endpoint equation, transpose by the composite source adjunction,
forget, and postcompose with chi. The normalized target adjunction identifies
the left side with the abelian transpose of forgetIso followed by the target
scalar adjunct. scalarUnit_abelianTranspose and scalarRoot_abelianTranspose
identify exactly these two abelian transposes with the corresponding source
arrows. Cancel chi, use faithfulness of Forget, and then injectivity of the
source Hom equivalence. No faithfulness of derived evaluation is used. -/
theorem ordinaryScalarAssociation_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit (l : Γ(X, ⊤))) (hY : IsUnit (l : Γ(Y, ⊤)))
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (nY : cY.Normalized l E) (nX : cX.Normalized l E)
    (θ₀ : CoefficientPullback l E b f g) (θ₁ : LinePullback l E f g cY cX)
    (d : IntegralCoefficientPullback l E f cY cX)
    (hk : ∀ n : ℕ, d.kummer.τ₂.app (Opposite.op n) =
      (unitsPull f).app (Opposite.op n))
    (eY : cY.scalar.model.E.obj (coefficient Y (Rrings l Y)) ⟶
      coefficient Y (Arings l E Y))
    (eX : cX.scalar.model.E.obj (coefficient X (Rrings l X)) ⟶
      coefficient X (Arings l E X))
    (heY : (cY.scalar.ordinaryAdjunction.homEquiv _ _) eY = scalarGenerator l E Y)
    (heX : (cX.scalar.ordinaryAdjunction.homEquiv _ _) eX = scalarGenerator l E X) :
    ∃ α : cY.scalar.model.E ⋙ g.pull ≅ d.pull ⋙ cX.scalar.model.E,
      α.hom.app (coefficient Y (Rrings l Y)) ≫ cX.scalar.model.E.map d.unitIso.hom ≫ eX =
        g.pull.map eY ≫ θ₀.iso.hom ∧
      α.hom.app cY.rootModule ≫ cX.scalar.model.E.map d.rootIso.hom = θ₁.iso.hom := by
  have _ := hX
  have _ := hY
  have _ := nY
  have _ := nX
  obtain ⟨χ, hχ, a, ha⟩ := restrictedScalarAdjunction_exists l E f b g cY cX d
  let aY := cY.scalar.ordinaryAdjunction.comp g.ordinaryAdjunction
  let α := aY.leftAdjointUniq a
  refine ⟨α, ?_, ?_⟩
  · apply (aY.homEquiv _ _).injective
    apply forget_map_injective Y (Rrings l Y) cY.reduction.forget
    apply (cancel_mono (χ.hom.app (coefficient X (Arings l E X)))).mp
    change cY.reduction.forget.F.map
        ((aY.homEquiv _ _) (α.hom.app _ ≫
          (cX.scalar.model.E.map d.unitIso.hom ≫ eX))) ≫ _ = _
    rw [comparison_transpose aY a]
    exact (ha _ _ _).trans
      (scalarUnit_abelianTranspose l E f b g cY cX d χ hχ θ₀ eY eX heY heX).symm
  · apply (aY.homEquiv _ _).injective
    apply forget_map_injective Y (Rrings l Y) cY.reduction.forget
    apply (cancel_mono (χ.hom.app (lineModule l E cX))).mp
    change cY.reduction.forget.F.map
        ((aY.homEquiv _ _) (α.hom.app _ ≫ cX.scalar.model.E.map d.rootIso.hom)) ≫ _ = _
    rw [comparison_transpose aY a]
    exact (ha _ _ _).trans
      (scalarRoot_abelianTranspose l E f b g cY cX d χ hχ hk θ₁).symm

end AlgebraicGeometry.ProEtale.SpTowerClasses
