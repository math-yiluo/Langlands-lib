/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSectionAdjoint
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TensorCoordinates.TowerClassTensorAdjointEvaluation

/-! # Coordinates for the normalized finite unit

Source: Stacks 03EL; Zheng Construction 4.1; blueprint tower-operations proof (2).
(blueprint: lem-sfb-tensor-comparison-unit-coordinates).
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

/-- The normalized underlying finite unit gives the actual system identity adjoint.
Source: blueprint tower-operations proof, clause (2), underlying unit normalization.
(blueprint: lem-sfb-tensor-comparison-unit-coordinates).

Proof: eliminate the specified coefficient, transition, pull-functor, finite adjunction
and pull-evaluation coordinate equalities. Evaluate the underlying-unit equation on x.
Use the identity-on-sections comparison for the direct image, then cancel the inverse
moduleUnderlying isomorphism. The evaluated system adjunction unit is the finite unit
followed by inverse pull-evaluation, by tensorComparison_adjoint_evaluation. This
identifies the transported section with sectionAdjoint of the identity, including on
empty charts and for zero modules. -/
theorem tensorComparison_unit_coordinates {b : SpTowerShriek.Base l E}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    (B' : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τ' : ∀ k, B' (k + 1) ⟶ B' k)
    (hB : B' = SpTowerShriek.B l E X) (hτ : HEq τ' (SpTowerShriek.tau l E X))
    (F : SpTowerShriek.S l E Y ⥤ SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ') (hF : HEq g.pull F) (n : ℕ)
    (q : Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (B' n),
      Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (B' n) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n), L ⊣ P)
    (hq : HEq q
      (⟨Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f,
        Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f,
        Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n),
          Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n) ⥤
            SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n), L ⊣ P))
    (cF : F ⋙ SemilinearSections.evaluation.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ' n ≅ SpTowerShriek.ev l E Y n ⋙ q.1)
    (hcF : HEq (g.ordinaryPullEvaluation n) cF)
    (e : q.1 ⋙ SemilinearSections.underlying.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (B' n) ≅
      SemilinearSections.underlying.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ⋙
          Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
    (d : q.2.1 ⋙ SemilinearSections.underlying.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ≅
      SemilinearSections.underlying.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (B' n) ⋙
          Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
    (hunit : ∀ M,
      (SemilinearSections.underlying.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).map (q.2.2.unit.app M) ≫
        d.hom.app (q.1.obj M) ≫
          (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).map (e.hom.app M) =
        (Scheme.proEtaleSheafAdjunction f (Type (u + 1))).unit.app
          ((SemilinearSections.underlying.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj M))
    (hpush : ∀ N (U : Y.ProEtᵒᵖ)
      (x : ((SemilinearSections.underlying.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj (q.2.1.obj N)).obj.obj U),
      HEq ((d.hom.app N).hom.app U x) x)
    (M : Systems Y (Arings l E Y)) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    HEq ((cF.inv.app M).val.app (chart f U)
      ((e.inv.app ((SpTowerShriek.ev l E Y n).obj M)).hom.app (chart f U)
        (((Scheme.proEtaleSheafAdjunction f (Type (u + 1))).unit.app
          ((SemilinearSections.underlying.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj
              ((SpTowerShriek.ev l E Y n).obj M))).hom.app U x)))
      (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x) := by
  subst B'
  cases eq_of_heq hτ
  cases eq_of_heq hF
  cases eq_of_heq hq
  cases eq_of_heq hcF
  have hη := congrArg (fun k ↦ k.hom.app U x)
    (hunit ((SpTowerShriek.ev l E Y n).obj M))
  change (e.hom.app ((SpTowerShriek.ev l E Y n).obj M)).hom.app (chart f U)
    ((d.hom.app ((Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).obj
      ((SpTowerShriek.ev l E Y n).obj M))).hom.app U
      (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
        ((SpTowerShriek.ev l E Y n).obj M)).val.app U x)) = _ at hη
  have hr := congrArg
    ((e.hom.app ((SpTowerShriek.ev l E Y n).obj M)).hom.app (chart f U))
    (eq_of_heq (hpush
      ((Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).obj
        ((SpTowerShriek.ev l E Y n).obj M)) U
      (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
        ((SpTowerShriek.ev l E Y n).obj M)).val.app U x)))
  have hη := hr.symm.trans hη
  have hi := congrArg ((e.inv.app ((SpTowerShriek.ev l E Y n).obj M)).hom.app (chart f U)) hη
  have hc := congrArg (fun k ↦ k.hom.app (chart f U)
    (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
      ((SpTowerShriek.ev l E Y n).obj M)).val.app U x))
      (e.hom_inv_id_app ((SpTowerShriek.ev l E Y n).obj M))
  have hu := hc.symm.trans hi
  have ha := congrArg (fun k ↦ k.val.app U x)
    (tensorComparison_adjoint_evaluation l E g (𝟙 (g.pull.obj M)) n)
  change sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x = _ at ha
  have ht := congrArg (fun k ↦ k.val.app U x)
    ((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv_unit
      _ _ ((g.ordinaryPullEvaluation n).inv.app M))
  apply heq_of_eq
  exact (congrArg (((g.ordinaryPullEvaluation n).inv.app M).val.app (chart f U)) hu).symm.trans
    (ha.trans ht).symm

end AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates
