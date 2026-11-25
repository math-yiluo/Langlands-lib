/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSectionAdjoint
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerOrdinaryUnitEvaluation

/-! # Evaluation of finite adjunction transposes

Source: Stacks 03EL; Zheng Construction 4.1; blueprint tower-operations proof (2).
(blueprint: lem-sfb-tensor-comparison-adjoint-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local implicit_reducible] SheafOfModules.toSheaf SheafOfModules.forget
attribute [local implicit_reducible] PresheafOfModules.toPresheaf CategoryTheory.sheafCompose
attribute [local implicit_reducible] PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj PresheafOfModules.presheaf ModuleCat.restrictScalars
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r u
open CategoryTheory.MonoidalCategory
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates
attribute [local irreducible] Scheme.proEtaleConstantRingComparison
  Scheme.proEtaleRingDirectImageMap Scheme.proEtaleRingModulePullback
  Scheme.proEtaleRingModuleAdjunction CategoryTheory.constantSheaf
  Padic Padic.coefficientExtensionIntegers SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
attribute [local implicit_reducible] spCoefficientCommRings SemilinearSections.evaluation
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj Scheme.proEtaleRingModuleDirectImage

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Evaluation commutes with transposition by the ordinary geometric adjunction.
Source: blueprint tower-operations proof, clause (2), normalization of the finite unit.
(blueprint: lem-sfb-tensor-comparison-adjoint-evaluation).

Proof: express transposition as the unit followed by the direct image of the map.
The normalized system unit evaluates to the finite unit followed by the direct image
of the inverse pull-evaluation isomorphism. Naturality of push-evaluation then gives
the finite transpose. This works without a nonempty chart or nonzero module assumption. -/
theorem tensorComparison_adjoint_evaluation {b : SpTowerShriek.Base l E}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    {M : Systems Y (Arings l E Y)} {N : Systems X (Arings l E X)}
    (h : g.pull.obj M ⟶ N) (n : ℕ) :
    (SpTowerShriek.ev l E Y n).map ((g.ordinaryAdjunction.homEquiv _ _) h) ≫
        (g.ordinaryPushEvaluation n).hom.app N =
      ((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
        ((g.ordinaryPullEvaluation n).inv.app M ≫ (SpTowerShriek.ev l E X n).map h) := by
  let P := Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f
  have hu := SpTowerShriek.geometry_unit_evaluation l E b g n M
  have hu' :
      (SpTowerShriek.ev l E Y n).map (g.ordinaryAdjunction.unit.app M) ≫
          (g.ordinaryPushEvaluation n).hom.app (g.pull.obj M) =
        (Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
          ((SpTowerShriek.ev l E Y n).obj M) ≫
            P.map ((g.ordinaryPullEvaluation n).inv.app M) := by
    apply (Iso.eq_comp_inv (P.mapIso ((g.ordinaryPullEvaluation n).app M))).2
    simpa only [P, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using hu
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  change _ ≫ ((g.push ⋙ SpTowerShriek.ev l E Y n).map h ≫ _) = _
  rw [(g.ordinaryPushEvaluation n).hom.naturality h, ← Category.assoc, hu']
  simp only [P, Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_map,
    Category.assoc]

private theorem adjoint_section {b : SpTowerShriek.Base l E}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    {M : Systems Y (Arings l E Y)} {N : Systems X (Arings l E X)}
    (h : g.pull.obj M ⟶ N) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
      ((g.ordinaryPullEvaluation n).inv.app M ≫ (SpTowerShriek.ev l E X n).map h)).val.app U
      x) = h.val.app (op (n, (chart f U).unop))
        (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x) := by
  have hn := congrArg (fun t ↦ t.val.app U x)
    ((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv_naturality_right
      ((g.ordinaryPullEvaluation n).inv.app M) ((SpTowerShriek.ev l E X n).map h))
  have hi := congrArg (fun t ↦ t.val.app U x)
    (tensorComparison_adjoint_evaluation l E g (𝟙 (g.pull.obj M)) n)
  exact hn.trans (congrArg (h.val.app (op (n, (chart f U).unop))) hi.symm)

end AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates
