/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSectionAdjoint

/-! # Naturality of sectionwise tower adjunction

Source: the ordinary evaluation comparison for strict coefficient systems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] lineModule
  Scheme.proEtaleConstantRingComparison Scheme.proEtaleRingDirectImageMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem evaluatedAdjoint_precomp
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {M M' : Systems Y (Arings l E Y)} {N : Systems X (Arings l E X)}
    (a : M' ⟶ M) (h : g.pull.obj M ⟶ N) (n : ℕ) :
    evaluatedAdjoint l E g (g.pull.map a ≫ h) n =
      (SpTowerShriek.ev l E Y n).map a ≫ evaluatedAdjoint l E g h n := by
  simp only [evaluatedAdjoint, ordinaryAdjoint,
    g.ordinaryAdjunction.homEquiv_naturality_left, Functor.map_comp, Category.assoc]

private theorem evaluatedAdjoint_postcomp
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {M : Systems Y (Arings l E Y)} {N N' : Systems X (Arings l E X)}
    (h : g.pull.obj M ⟶ N) (a : N ⟶ N') (n : ℕ) :
    evaluatedAdjoint l E g (h ≫ a) n = evaluatedAdjoint l E g h n ≫
      (Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).map
        ((SpTowerShriek.ev l E X n).map a) := by
  simp only [evaluatedAdjoint, ordinaryAdjoint,
    g.ordinaryAdjunction.homEquiv_naturality_right, Functor.map_comp, Category.assoc]
  exact congrArg
    (fun k ↦ (SpTowerShriek.ev l E Y n).map (ordinaryAdjoint l E g h) ≫ k)
    ((g.ordinaryPushEvaluation n).hom.naturality a)

/-- Naturality of section adjunction in the source.
Source: ordinary adjunction naturality and evaluation.
(blueprint: lem-sfb-tower-class-section-adjoint-naturality). -/
theorem sectionAdjoint_precomp
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {M M' : Systems Y (Arings l E Y)} {N : Systems X (Arings l E X)}
    (a : M' ⟶ M) (h : g.pull.obj M ⟶ N) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : M'.val.obj (op (n, U.unop))) :
    sectionAdjoint l E g (g.pull.map a ≫ h) n U x =
      sectionAdjoint l E g h n U (a.val.app (op (n, U.unop)) x) := by
  exact congrArg (fun k ↦ k.val.app U x) (evaluatedAdjoint_precomp l E g a h n)

/-- Naturality of section adjunction in the target.
Source: ordinary adjunction and the ordinary push-evaluation comparison.
(blueprint: lem-sfb-tower-class-section-adjoint-naturality). -/
theorem sectionAdjoint_postcomp
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {M : Systems Y (Arings l E Y)} {N N' : Systems X (Arings l E X)}
    (h : g.pull.obj M ⟶ N) (a : N ⟶ N') (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    sectionAdjoint l E g (h ≫ a) n U x =
      a.val.app (op (n, (chart f U).unop)) (sectionAdjoint l E g h n U x) := by
  unfold sectionAdjoint adjointSection
  erw [evaluatedAdjoint_postcomp]
  rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses
