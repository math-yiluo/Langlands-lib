/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassDiagonal
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteUnit
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSectionGeometryExistence
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassUnitSuccessorCompatibility

/-! # Compatible finite coordinates for the coefficient unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe a b w u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
  CategoryTheory.constantSheaf Padic Padic.coefficientExtensionIntegers

private theorem transition_sections
    {C : Type a} [Category.{b} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{w} C] (B : ℕ → Sheaf J CommRingCat.{w}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {m n : ℕ} (h : n ≤ m) (M : SemilinearSections.Systems.{a, b, w} J B τ)
    (U : Cᵒᵖ) (x : M.val.obj (op (m, U.unop))) :
    ((SemilinearSections.transition J B τ h).app M).val.app U x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x :=
  congrFun (eq_of_heq ((SemilinearSections.transition_exists J B τ h).exists.choose_spec
    M U)) x

private theorem compatible_of_successor
    {C : Type a} [Category.{b} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{w} C] (B : ℕ → Sheaf J CommRingCat.{w}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {M N : SemilinearSections.Systems.{a, b, w} J B τ}
    (d : ∀ n, (SemilinearSections.evaluation J B τ n).obj M ⟶
      (SemilinearSections.evaluation J B τ n).obj N)
    (hs : ∀ n, (SemilinearSections.transition J B τ (Nat.le_succ n)).app M ≫
      (SemilinearSections.res (SemilinearSections.coefficientMap J B τ
        (Nat.le_succ n))).map (d n) =
      d (n + 1) ≫ (SemilinearSections.transition J B τ (Nat.le_succ n)).app N) :
    ∀ {m n : ℕ} (h : n ≤ m), (SemilinearSections.transition J B τ h).app M ≫
      (SemilinearSections.res (SemilinearSections.coefficientMap J B τ h)).map (d n) =
      d m ≫ (SemilinearSections.transition J B τ h).app N := by
  intro m n h
  ext U x
  change (d n).val.app U (((SemilinearSections.transition J B τ h).app M).val.app U x) =
    ((SemilinearSections.transition J B τ h).app N).val.app U ((d m).val.app U x)
  let FM := (Prod.sectL ℕ U.unop).op ⋙ M.val.presheaf ⋙ forget AddCommGrpCat.{w}
  let FN := (Prod.sectL ℕ U.unop).op ⋙ N.val.presheaf ⋙ forget AddCommGrpCat.{w}
  let α : FM ⟶ FN := NatTrans.ofOpSequence
    (fun k ↦ TypeCat.ofHom (fun y ↦ (d k).val.app U y))
    (fun k ↦ by
      ext y
      have hh := congrArg (fun q ↦ q.val.app U y) (hs k)
      change (d k).val.app U
        (((SemilinearSections.transition J B τ (Nat.le_succ k)).app M).val.app U y) =
        ((SemilinearSections.transition J B τ (Nat.le_succ k)).app N).val.app U
          ((d (k + 1)).val.app U y) at hh
      exact (congrArg (fun z ↦ (d k).val.app U z)
        (transition_sections J B τ (Nat.le_succ k) M U y).symm).trans
          (hh.trans (transition_sections J B τ (Nat.le_succ k) N U
            ((d (k + 1)).val.app U y))))
  have ha := ConcreteCategory.congr_hom (α.naturality (homOfLE h).op) x
  exact (congrArg (fun z ↦ (d n).val.app U z)
    (transition_sections J B τ h M U x)).trans
      (ha.trans (transition_sections J B τ h N U ((d m).val.app U x)).symm)

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Finite free-rank-one pullback maps commute with the actual quotient transitions.

Source: Stacks 03D2, 03EL, and the unit construction in blueprint
`sk-lem-sp-tower-bound-operations.proof.md`, clause (2).
(blueprint: lem-sfb-tower-class-unit-level-coordinates).

Proof: use the coefficient calculus and Base of strictSystemGeometricRealization.
Construct the ordinary geometry on the ringed sequence site using the canonical
constant-section presentations at every level, then derive these functors using
the same K-injective and K-flat constructions as semilinearGeometryBaseExistence.
The level functors and their adjunctions are the actual constant-ring operations,
and the level direct-image underlying comparisons act identically on sections.
Use these presentations before making the derived geometry: an arbitrary geometry
can have unrelated underlying-coordinate automorphisms.
At level n use pullback of the rank-one module, with its map to the target
rank-one module sending the pullback of a coefficient section to its constant
restriction. In the small site model this is pullbackObjUnitToUnit, followed by
the canonical constant-ring comparison and scalar-extension multiplication.
Both factors are isomorphisms, including on the empty chart. Transport through
the fixed ordinary pull-evaluation comparison to obtain delta_n. Its finite
adjoint is the constant direct-image map, by the unit normalization of the actual
constant-ring adjunction. For m >= n, transpose the two horizontal composites
with the level-m adjunction. The recorded ordinaryPullTransition formula and
naturality of constant sheafification identify both with restriction along the
same quotient R_m -> R_n followed by constant direct image. Injectivity of the
adjunction transpose proves the horizontal equation. This constructs only finite
maps and their compatibility; it does not assemble a system isomorphism. -/
theorem exists_unitLevelCoordinates {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ b : SpTowerShriek.Base l E, ∃ g : SpTowerShriek.Geometry l E b f,
      (∀ (n : ℕ)
        (N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (g.generic.coefficients n)) (U : Y.ProEtᵒᵖ)
        (x : ((SemilinearSections.underlying.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj
            ((g.generic.levelPush n).obj N)).obj.obj U),
        HEq (((g.generic.levelPushUnderlying n).hom.app N).hom.app U x) x) ∧ ∃ δ : ∀ n : ℕ,
      (SpTowerShriek.ev l E X n).obj
          (g.pull.obj (coefficient Y (Arings l E Y))) ≅
        (SpTowerShriek.ev l E X n).obj (coefficient X (Arings l E X)),
      (∀ {m n : ℕ} (h : n ≤ m),
        (SemilinearSections.transition (Scheme.ProEt.topology X)
            (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).app
            (g.pull.obj (coefficient Y (Arings l E Y))) ≫
          (SemilinearSections.res (SemilinearSections.coefficientMap
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
            (SpTowerShriek.tau l E X) h)).map (δ n).hom =
        (δ m).hom ≫ (SemilinearSections.transition (Scheme.ProEt.topology X)
          (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).app
            (coefficient X (Arings l E X))) ∧
      ∀ (n : ℕ) (U : Y.ProEtᵒᵖ)
        (x : (SpTowerShriek.B l E Y n).obj.obj U)
        (x' : ((SpTowerShriek.ev l E Y n).obj
          (coefficient Y (Arings l E Y))).val.obj U),
        HEq x x' → HEq
          ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv
            _ _) ((g.ordinaryPullEvaluation n).inv.app
              (coefficient Y (Arings l E Y)) ≫ (δ n).hom)).val.app U x')
          ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} f CommRingCat.{u + 1}
            (CommRingCat.of.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app
              U x) := by
  classical
  obtain ⟨b, g, hpush⟩ := exists_sectionGeometry l E f
  have hfinite := exists_finiteUnitIso l E f
  choose d hd using hfinite
  let δ (n : ℕ) :=
    (g.ordinaryPullEvaluation n).app (coefficient Y (Arings l E Y)) ≪≫ d n
  have hnorm : ∀ (n : ℕ) (U : Y.ProEtᵒᵖ)
      (x : (SpTowerShriek.B l E Y n).obj.obj U)
      (x' : ((SpTowerShriek.ev l E Y n).obj
        (coefficient Y (Arings l E Y))).val.obj U),
      HEq x x' → HEq
        ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv
          _ _) ((g.ordinaryPullEvaluation n).inv.app
            (coefficient Y (Arings l E Y)) ≫ (δ n).hom)).val.app U x')
        ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app U x) := by
    intro n U x x' hx
    have hc : (g.ordinaryPullEvaluation n).inv.app
        (coefficient Y (Arings l E Y)) ≫ (δ n).hom = (d n).hom :=
      Iso.inv_hom_id_assoc ((g.ordinaryPullEvaluation n).app
        (coefficient Y (Arings l E Y))) (d n).hom
    exact (heq_of_eq (congrArg (fun q ↦
      (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv
        _ _) q).val.app U x') hc)).trans (hd n U x x' hx)
  refine ⟨b, g, hpush, δ, ?_, hnorm⟩
  exact compatible_of_successor (Scheme.ProEt.topology X)
    (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) (fun n ↦ (δ n).hom)
    (unit_successor_compatibility l E g hpush (fun n ↦ (δ n).hom) hnorm)

end AlgebraicGeometry.ProEtale.SpTowerClasses
