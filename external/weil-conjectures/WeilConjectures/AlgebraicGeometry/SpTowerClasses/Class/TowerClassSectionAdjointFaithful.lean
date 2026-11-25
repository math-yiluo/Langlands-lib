/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSectionAdjoint

/-! # Faithfulness of sectionwise tower adjunction

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

/-- Section adjunction detects equality of ordinary arrows.

Source: the ordinary adjunction and invertibility of ordinaryPushEvaluation.
Transpose, test maps of sheaves sectionwise, and cancel the evaluation comparison.
(blueprint: lem-sfb-tower-class-section-adjoint-faithful). -/
theorem sectionAdjoint_ext
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {M : Systems Y (Arings l E Y)} {N : Systems X (Arings l E X)}
    {a b' : g.pull.obj M ⟶ N}
    (h : ∀ (n : ℕ) (U : Y.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))),
      sectionAdjoint l E g a n U x = sectionAdjoint l E g b' n U x) : a = b' := by
  apply (g.ordinaryAdjunction.homEquiv M N).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  obtain ⟨n, U, rfl⟩ : ∃ (n : ℕ) (U : Y.ProEt), W = op (n, U) :=
    ⟨W.unop.1, W.unop.2, rfl⟩
  let e := (g.ordinaryPushEvaluation n).app N
  have hi : Function.Injective (e.hom.val.app (op U)) := by
    apply Function.LeftInverse.injective (g := e.inv.val.app (op U))
    intro z
    exact congrArg (fun k ↦ k.val.app (op U) z) e.hom_inv_id
  apply hi
  exact h n (op U) x

end AlgebraicGeometry.ProEtale.SpTowerClasses
