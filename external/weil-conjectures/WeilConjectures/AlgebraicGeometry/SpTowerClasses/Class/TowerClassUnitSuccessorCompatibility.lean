/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients

/-! # Quotient compatibility of normalized finite unit maps -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
-- Reduce forgetful wrappers without expanding the coefficient-ring constructions.
attribute [local implicit_reducible] SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
universe u c v r
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearSections.evaluation SemilinearSections.transition
  SemilinearSections.coefficientMap
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
  CategoryTheory.constantSheaf Padic Padic.coefficientExtensionIntegers

attribute [local implicit_reducible] SheafOfModules.toSheaf SheafOfModules.forget
  PresheafOfModules.toPresheaf CategoryTheory.sheafCompose
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj PresheafOfModules.presheaf
  ModuleCat.restrictScalars

namespace UnitSuccessorProof

open SemilinearSections

-- Give the forgotten transition its exact source and target before specializing rings.
private def horizontalUnderlying
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max c v r} C]
    (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {m n : ℕ} (h : n ≤ m) (M : Systems.{c, v, max c v r} J B τ) :
    (underlying.{c, v, r} J (B m)).obj ((evaluation J B τ m).obj M) ⟶
      (underlying.{c, v, r} J (B n)).obj ((evaluation J B τ n).obj M) :=
  (underlying.{c, v, r} J (B m)).map ((transition J B τ h).app M)

private theorem horizontal_apply
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max c v r} C]
    (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {m n : ℕ} (h : n ≤ m) (M : Systems.{c, v, max c v r} J B τ)
    (U : Cᵒᵖ) (x : ((evaluation J B τ m).obj M).val.obj U) :
    HEq (((horizontalUnderlying.{c, v, r} J B τ h M).hom.app U) x)
      (((transition J B τ h).app M).val.app U x) := by rfl

private theorem square_of_underlying
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max c v r} C]
    (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {m n : ℕ} (h : n ≤ m) (M N : Systems.{c, v, max c v r} J B τ)
    (d₀ : (evaluation J B τ n).obj M ⟶ (evaluation J B τ n).obj N)
    (d₁ : (evaluation J B τ m).obj M ⟶ (evaluation J B τ m).obj N)
    (H : horizontalUnderlying.{c, v, r} J B τ h M ≫ (underlying.{c, v, r} J (B n)).map d₀ =
      (underlying.{c, v, r} J (B m)).map d₁ ≫ horizontalUnderlying.{c, v, r} J B τ h N) :
    (transition J B τ h).app M ≫ (res (coefficientMap J B τ h)).map d₀ =
      d₁ ≫ (transition J B τ h).app N := by
  apply (underlying.{c, v, r} J (B m)).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  exact H

section Generic
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
  (A : Data.{c, v, r} J B τ)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (L : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (P : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (a : L ⊣ P) (G : Geometry.{c, v, r} J B τ A J' L P a)

private def image (n : ℕ) (M : Systems.{c, v, max c v r} J B τ) :
    (underlying.{c, v, r} J' (G.coefficients n)).obj
        ((evaluation J' G.coefficients G.coefficientTransition n).obj (G.pull.obj M)) ≅
      L.obj ((underlying.{c, v, r} J (B n)).obj ((evaluation J B τ n).obj M)) :=
  (underlying.{c, v, r} J' (G.coefficients n)).mapIso
      ((G.ordinaryPullEvaluation n).app M) ≪≫
    (G.inverseImage n).moduleUnderlying.app _

private theorem horizontal {m n : ℕ} (h : n ≤ m)
    (M : Systems.{c, v, max c v r} J B τ) :
    horizontalUnderlying.{c, v, r} J' G.coefficients G.coefficientTransition h (G.pull.obj M) ≫
      (image J B τ A J' L P a G n M).hom =
    (image J B τ A J' L P a G m M).hom ≫
      L.map (horizontalUnderlying.{c, v, r} J B τ h M) := by
  let U := underlying.{c, v, r} J' (G.coefficients m)
  let t := (transition J' G.coefficients G.coefficientTransition h).app (G.pull.obj M)
  let e := (G.ordinaryPullEvaluation n).hom.app M
  let d := (transition J B τ h).app M
  let b := (G.restrictionPullback h).hom.app ((evaluation J B τ n).obj M)
  calc
    _ = U.map (t ≫ (res (coefficientMap J' G.coefficients
        G.coefficientTransition h)).map e) ≫
        (G.inverseImage n).moduleUnderlying.hom.app _ := by
      simp only [Functor.map_comp, Category.assoc]
      rfl
    _ = U.map ((G.ordinaryPullEvaluation m).hom.app M ≫
        (G.inverseImage m).modules.map d ≫ b) ≫
        (G.inverseImage n).moduleUnderlying.hom.app _ :=
      congrArg (fun k ↦ U.map k ≫ (G.inverseImage n).moduleUnderlying.hom.app _)
        (G.ordinaryPullTransition h M)
    _ = U.map ((G.ordinaryPullEvaluation m).hom.app M) ≫
        U.map ((G.inverseImage m).modules.map d) ≫
          (U.map b ≫ (G.inverseImage n).moduleUnderlying.hom.app _) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = U.map ((G.ordinaryPullEvaluation m).hom.app M) ≫
        U.map ((G.inverseImage m).modules.map d) ≫
          (G.inverseImage m).moduleUnderlying.hom.app _ :=
      congrArg (fun k ↦ U.map ((G.ordinaryPullEvaluation m).hom.app M) ≫
        U.map ((G.inverseImage m).modules.map d) ≫ k)
          (G.restrictionPullback_underlying h _)
    _ = _ := congrArg (fun k ↦ U.map ((G.ordinaryPullEvaluation m).hom.app M) ≫ k)
      ((G.inverseImage m).moduleUnderlying.hom.naturality d)

private theorem transpose (n : ℕ) (M : SemilinearSections.Mod.{c, v, max c v r} J (B n))
    (N : SemilinearSections.Mod.{c, v, max c v r} J' (G.coefficients n))
    (f : (G.inverseImage n).modules.obj M ⟶ N) :
    (underlying.{c, v, r} J (B n)).map ((G.levelAdjunction n).homEquiv _ _ f) ≫
      (G.levelPushUnderlying n).hom.app N =
    a.homEquiv _ _ ((G.inverseImage n).moduleUnderlying.inv.app M ≫
      (underlying.{c, v, r} J' (G.coefficients n)).map f) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  have hn := (G.levelPushUnderlying n).hom.naturality f
  change (underlying.{c, v, r} J (B n)).map ((G.levelPush n).map f) ≫
      (G.levelPushUnderlying n).hom.app N =
    (G.levelPushUnderlying n).hom.app ((G.inverseImage n).modules.obj M) ≫
      P.map ((underlying.{c, v, r} J' (G.coefficients n)).map f) at hn
  rw [Category.assoc, hn]
  change _ = _ ≫ P.map _
  rw [← G.level_unit_underlying n M, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]

end Generic
private theorem square_of_transposes
    {C : Type*} [Category C] {D : Type*} [Category D]
    {L : C ⥤ D} {P : D ⥤ C} (a : L ⊣ P)
    {M₀ M₁ : C} {V₀ V₁ N₀ N₁ : D}
    (e₀ : V₀ ≅ L.obj M₀) (e₁ : V₁ ≅ L.obj M₁)
    (s : M₁ ⟶ M₀) (t : V₁ ⟶ V₀) (u : N₁ ⟶ N₀)
    (d₀ : V₀ ⟶ N₀) (d₁ : V₁ ⟶ N₁)
    (ht : t ≫ e₀.hom = e₁.hom ≫ L.map s)
    (ha : s ≫ a.homEquiv _ _ (e₀.inv ≫ d₀) =
      a.homEquiv _ _ (e₁.inv ≫ d₁) ≫ P.map u) :
    t ≫ d₀ = d₁ ≫ u := by
  have hd : L.map s ≫ (e₀.inv ≫ d₀) = (e₁.inv ≫ d₁) ≫ u := by
    apply (a.homEquiv _ _).injective
    exact (a.homEquiv_naturality_left s (e₀.inv ≫ d₀)).trans
      (ha.trans (a.homEquiv_naturality_right (e₁.inv ≫ d₁) u).symm)
  apply (cancel_epi e₁.inv).mp
  have hti : e₁.inv ≫ t = L.map s ≫ e₀.inv := by
    apply (cancel_mono e₀.hom).mp
    calc
      (e₁.inv ≫ t) ≫ e₀.hom = e₁.inv ≫ (t ≫ e₀.hom) := Category.assoc _ _ _
      _ = e₁.inv ≫ (e₁.hom ≫ L.map s) := congrArg (e₁.inv ≫ ·) ht
      _ = L.map s := e₁.inv_hom_id_assoc _
      _ = (L.map s ≫ e₀.inv) ≫ e₀.hom := by
        rw [Category.assoc, e₀.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hti]
  exact (Category.assoc _ _ _).trans (hd.trans (Category.assoc _ _ _))

end UnitSuccessorProof

namespace AlgebraicGeometry.ProEtale.SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local implicit_reducible] spCoefficientCommRings
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence

-- Direct image is precomposition on underlying sections.
private def pushUnderlying {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (SpTowerShriek.B l E X n)) :
    (SemilinearSections.underlying.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj
      ((Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).obj N) ≅
    (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).obj
      ((SemilinearSections.underlying.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n)).obj N) := Iso.refl _

private def pushMap {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    {M : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology Y)
      (SpTowerShriek.B l E Y n)}
    {N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (SpTowerShriek.B l E X n)}
    (d : M ⟶ (Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).obj N) :
    (SemilinearSections.underlying.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj M ⟶
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).obj
        ((SemilinearSections.underlying.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n)).obj N) :=
  (SemilinearSections.underlying.{u + 1, u, u + 1}
    (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).map d ≫
      (pushUnderlying l E f n N).hom

private theorem pushMap_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    {M : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology Y)
      (SpTowerShriek.B l E Y n)}
    {N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (SpTowerShriek.B l E X n)}
    (d : M ⟶ (Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).obj N)
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    HEq (((pushMap l E f n d).hom.app U) x) (d.val.app U x) := by rfl

-- Transport the generic geometry formulas through the recorded presentation equalities.
private theorem coordinates
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f)
    (C : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n)
    (hC : C = SpTowerShriek.B l E X) (hτ : HEq τ (SpTowerShriek.tau l E X))
    (F : SpTowerShriek.S l E Y ⥤
      SemilinearSections.Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology X) C τ)
    (hF : HEq F g.pull)
    (q : ∀ n, Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (C n),
      Σ P : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (C n) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n), L ⊣ P)
    (hq : ∀ n, HEq (q n)
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
    (e : ∀ n, F ⋙ SemilinearSections.evaluation (Scheme.ProEt.topology X) C τ n ≅
      SpTowerShriek.ev l E Y n ⋙ (q n).1)
    (he : ∀ n, HEq (e n) (g.ordinaryPullEvaluation n))
    (i : ∀ n, (q n).1 ⋙
        SemilinearSections.underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (C n) ≅
      SemilinearSections.underlying.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ⋙
      Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
    (v : ∀ n, (q n).2.1 ⋙
        SemilinearSections.underlying.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ≅
      SemilinearSections.underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (C n) ⋙
        Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
    (hv : ∀ n N U (x : ((SemilinearSections.underlying.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj
          ((q n).2.1.obj N)).obj.obj U),
      HEq (((v n).hom.app N).hom.app U x) x)
    (ht : ∀ (n : ℕ)
      (M : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n))
      (N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (C n))
      (d : (q n).1.obj M ⟶ N),
      (SemilinearSections.underlying.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).map
          ((q n).2.2.homEquiv _ _ d) ≫ (v n).hom.app N =
        (Scheme.proEtaleSheafAdjunction f (Type (u + 1))).homEquiv _ _
          ((i n).inv.app M ≫
            (SemilinearSections.underlying.{u + 1, u, u + 1}
              (Scheme.ProEt.topology X) (C n)).map d))
    (M : SpTowerShriek.S l E Y)
    (hh : ∀ n,
      (UnitSuccessorProof.horizontalUnderlying.{u + 1, u, u + 1} (Scheme.ProEt.topology X) C τ
        (Nat.le_succ n) (F.obj M)) ≫
        ((SemilinearSections.underlying.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (C n)).mapIso ((e n).app M) ≪≫
            (i n).app ((SpTowerShriek.ev l E Y n).obj M)).hom =
      ((SemilinearSections.underlying.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (C (n + 1))).mapIso ((e (n + 1)).app M) ≪≫
            (i (n + 1)).app ((SpTowerShriek.ev l E Y (n + 1)).obj M)).hom ≫
        (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
          ((UnitSuccessorProof.horizontalUnderlying.{u + 1, u, u + 1} (Scheme.ProEt.topology Y)
            (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) (Nat.le_succ n) M))) :
    ∃ j : ∀ n,
      (SemilinearSections.underlying.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n)).obj
          ((SpTowerShriek.ev l E X n).obj (g.pull.obj M)) ≅
        (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).obj
          ((SemilinearSections.underlying.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj
              ((SpTowerShriek.ev l E Y n).obj M)),
      (∀ n,
        (UnitSuccessorProof.horizontalUnderlying.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X)
          (Nat.le_succ n) (g.pull.obj M)) ≫ (j n).hom =
          (j (n + 1)).hom ≫
            (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
              ((UnitSuccessorProof.horizontalUnderlying.{u + 1, u, u + 1} (Scheme.ProEt.topology Y)
                (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) (Nat.le_succ n) M))) ∧
      ∀ (n : ℕ) (N : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n))
        (d : (SpTowerShriek.ev l E X n).obj (g.pull.obj M) ⟶ N),
        pushMap l E f n
            ((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv
              ((SpTowerShriek.ev l E Y n).obj M) N
              ((g.ordinaryPullEvaluation n).inv.app M ≫ d)) =
          (Scheme.proEtaleSheafAdjunction f (Type (u + 1))).homEquiv _ _
            ((j n).inv ≫
              (SemilinearSections.underlying.{u + 1, u, u + 1}
                (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n)).map d) := by
  subst C
  have hτ' : τ = SpTowerShriek.tau l E X := eq_of_heq hτ
  subst τ
  have hF' : F = g.pull := eq_of_heq hF
  subst F
  have hq' : q = fun n ↦
      ⟨Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f,
        Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f,
        Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f⟩ :=
    funext fun n ↦ eq_of_heq (hq n)
  subst q
  have he' : e = g.ordinaryPullEvaluation := funext fun n ↦ eq_of_heq (he n)
  subst e
  refine ⟨fun n ↦
    (SemilinearSections.underlying.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n)).mapIso
        ((g.ordinaryPullEvaluation n).app M) ≪≫
      (i n).app ((SpTowerShriek.ev l E Y n).obj M), hh, ?_⟩
  intro n N d
  have hv' : (v n).hom.app N = (pushUnderlying l E f n N).hom := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    exact eq_of_heq (hv n N U x)
  have ht' := ht n ((SpTowerShriek.ev l E Y n).obj M) N
    ((g.ordinaryPullEvaluation n).inv.app M ≫ d)
  rw [hv'] at ht'
  simpa only [pushMap, Functor.map_comp, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    Category.assoc] using ht'

section ConstantNaturality
attribute [local semireducible] CategoryTheory.constantSheaf
attribute [local implicit_reducible] CategoryTheory.constantSheaf

private theorem constant_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (ρ : A ⟶ B) :
    (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map ρ ≫
        Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} B =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A ≫
        (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map ρ) := by
  let a := sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}
  apply (a.homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
    ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj B))).injective
  change ((sheafificationAdjunction (Scheme.ProEt.topology Y)
    CommRingCat.{u + 1}).homEquiv _ _)
    (((presheafToSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map
      ((Functor.const Y.ProEtᵒᵖ).map ρ)) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  unfold Scheme.proEtaleConstantDirectImageMap
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg (fun k ↦ k.app ((Scheme.proEtaleBaseChange f).op.obj U))
    (toSheafify_naturality (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map ρ))

end ConstantNaturality

section CoefficientSections
attribute [local semireducible] SemilinearSections.coefficientMap
attribute [local semireducible] SemilinearSections.evaluation SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
attribute [local implicit_reducible] SemilinearSections.evaluation SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings

private theorem coefficient_transition_sections (T : Scheme.{u}) {m n : ℕ}
    (h : n ≤ m) (U : T.ProEtᵒᵖ) (x : (SpTowerShriek.B l E T m).obj.obj U) :
    ((SemilinearSections.transition (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app
        (coefficient T (Arings l E T))).val.app U x =
      (SemilinearSections.coefficientMap (Scheme.ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).hom.app U x := by
  have ht := congrFun (eq_of_heq
    ((SemilinearSections.transition_exists (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).exists.choose_spec
        (coefficient T (Arings l E T)) U)) x
  unfold SemilinearSections.transition
  refine ht.trans ?_
  unfold coefficient Arings SemilinearSections.coefficientMap
  change (SpTowerShriek.B l E T n).obj.map (𝟙 U)
    ((SemilinearSections.coefficientMap (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).hom.app U x) = _
  exact congrArg (fun k ↦ k
    ((SemilinearSections.coefficientMap (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).hom.app U x))
    ((SpTowerShriek.B l E T n).obj.map_id U)

private theorem coefficient_carrier (T : Scheme.{u}) (n : ℕ) (U : T.ProEtᵒᵖ) :
    (((SpTowerShriek.ev l E T n).obj
      (coefficient T (Arings l E T))).val.obj U : Type (u + 1)) =
      ((SpTowerShriek.B l E T n).obj.obj U : Type (u + 1)) := by rfl

private theorem coefficient_horizontal_sections (T : Scheme.{u}) {m n : ℕ}
    (h : n ≤ m) (U : T.ProEtᵒᵖ)
    (x : (SpTowerShriek.B l E T m).obj.obj U)
    (x' : ((SpTowerShriek.ev l E T m).obj
      (coefficient T (Arings l E T))).val.obj U) (hx : HEq x x') :
    HEq
      (((UnitSuccessorProof.horizontalUnderlying.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
        h (coefficient T (Arings l E T))).hom.app U) x')
      ((SemilinearSections.coefficientMap (Scheme.ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).hom.app U x) := by
  have hxx : x' = x := (eq_of_heq hx).symm
  subst x'
  exact (UnitSuccessorProof.horizontal_apply.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
      h (coefficient T (Arings l E T)) U x).trans
        (heq_of_eq (coefficient_transition_sections l E T h U x))

private theorem coefficient_ring_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (U : Y.ProEtᵒᵖ) (x : (SpTowerShriek.B l E Y (n + 1)).obj.obj U) :
    (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app U
        ((SemilinearSections.coefficientMap (Scheme.ProEt.topology Y)
          (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y)
          (Nat.le_succ n)).hom.app U x) =
    (SemilinearSections.coefficientMap (Scheme.ProEt.topology X)
      (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) (Nat.le_succ n)).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U)
        ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E (n + 1))))).hom.app U x) := by
  simp only [SemilinearSections.coefficientMap, SemilinearSections.rings,
    Functor.ofOpSequence_map_homOfLE_succ, SpTowerShriek.tau,
    spCoefficientCommRings, Functor.ofOpSequence_map_homOfLE_succ]
  exact (ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.hom.app U) (constant_naturality f
      (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{u + 1} (SpTowerShriek.R l E n) ≃+*
          SpTowerShriek.R l E n).symm.toRingHom.comp
          ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
            (ULift.ringEquiv : ULift.{u + 1} (SpTowerShriek.R l E (n + 1)) ≃+*
              SpTowerShriek.R l E (n + 1)).toRingHom))))) x)

end CoefficientSections

private theorem pushMap_normalized {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (d : (SpTowerShriek.ev l E Y n).obj (coefficient Y (Arings l E Y)) ⟶
      (Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).obj
        ((SpTowerShriek.ev l E X n).obj (coefficient X (Arings l E X))))
    (hd : ∀ (U : Y.ProEtᵒᵖ) (x : (SpTowerShriek.B l E Y n).obj.obj U)
      (x' : ((SpTowerShriek.ev l E Y n).obj
        (coefficient Y (Arings l E Y))).val.obj U), HEq x x' → HEq (d.val.app U x')
      ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app U x))
    (U : Y.ProEtᵒᵖ) (x : (SpTowerShriek.B l E Y n).obj.obj U)
    (x' : ((SpTowerShriek.ev l E Y n).obj
      (coefficient Y (Arings l E Y))).val.obj U) (hx : HEq x x') :
    HEq (((pushMap l E f n d).hom.app U) x')
      ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app U x) :=
  (pushMap_apply l E f n d U x').trans (hd U x x' hx)

private theorem normalized_naturality
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (t : ∀ n : ℕ, (SpTowerShriek.ev l E Y n).obj
        (coefficient Y (Arings l E Y)) ⟶
      (Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).obj
        ((SpTowerShriek.ev l E X n).obj (coefficient X (Arings l E X))))
    (hnorm : ∀ (n : ℕ) (U : Y.ProEtᵒᵖ)
        (x : (SpTowerShriek.B l E Y n).obj.obj U)
        (x' : ((SpTowerShriek.ev l E Y n).obj
          (coefficient Y (Arings l E Y))).val.obj U),
        HEq x x' → HEq
          ((t n).val.app U x')
          ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} f CommRingCat.{u + 1}
            (CommRingCat.of.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app
              U x))
    (n : ℕ) :
    UnitSuccessorProof.horizontalUnderlying.{u + 1, u, u + 1} (Scheme.ProEt.topology Y)
        (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) (Nat.le_succ n)
        (coefficient Y (Arings l E Y)) ≫ pushMap l E f n (t n) =
      pushMap l E f (n + 1) (t (n + 1)) ≫
        (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).map
          (UnitSuccessorProof.horizontalUnderlying.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
            (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) (Nat.le_succ n)
              (coefficient X (Arings l E X))) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  let x₀ := cast (coefficient_carrier l E Y (n + 1) U) x
  have hx₀ : HEq x₀ x := cast_heq _ _
  have hsY := coefficient_horizontal_sections l E Y (Nat.le_succ n) U x₀ x hx₀
  have hp₀ := pushMap_normalized l E f n (t n) (hnorm n) U
    ((SemilinearSections.coefficientMap (Scheme.ProEt.topology Y)
      (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) (Nat.le_succ n)).hom.app U x₀)
    _ hsY.symm
  have hp₁ := pushMap_normalized l E f (n + 1) (t (n + 1)) (hnorm (n + 1)) U x₀ x hx₀
  have hsX := coefficient_horizontal_sections l E X (Nat.le_succ n)
    ((Scheme.proEtaleBaseChange f).op.obj U)
    ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E (n + 1))))).hom.app U x₀)
    _ hp₁.symm
  exact eq_of_heq (hp₀.trans
    ((heq_of_eq (coefficient_ring_naturality l E f n U x₀)).trans hsX.symm))

/-- The adjacent horizontal equation for already supplied finite maps, without an
existence or invertibility assertion.
Source: Stacks 03D2, 03D7; Zheng Construction 4.1; blueprint
`sk-lem-sp-tower-bound-operations.proof.md`, clause (2).
(blueprint: lem-sfb-tower-class-unit-successor-compatibility).

Proof: apply ordinaryPullTransition to the source coefficient system. After
conjugating by ordinaryPullEvaluation the proposed square becomes the square
between pullback of the quotient map followed by restrictionPullback, and the
quotient map on the target regular modules. Transpose at level n + 1. The level unit
underlying equation identifies the transpose with the original set-sheaf
adjunction, since levelPushUnderlying is identity on sections. The underlying
normalization of restrictionPullback moves the restriction edge through this
transpose. Substitute the assumed formulas for the transposes of the two finite
maps. Naturality of proEtaleConstantDirectImageMap in the coefficient ring shows
that both resulting maps are the same constant direct-image map composed with
the quotient R_(n+1) to R_n. Faithfulness of the underlying module functor and
injectivity of the adjunction Hom equivalence give the square. Conjugating back
cancels the evaluation isomorphisms. The argument uses unital maps, including
on empty charts, and needs no flatness
or inverse of a quotient map. -/
theorem unit_successor_compatibility {X Y : Scheme.{u}} {f : X ⟶ Y}
    {b : SpTowerShriek.Base l E} (g : SpTowerShriek.Geometry l E b f)
    (hpush : ∀ (n : ℕ)
        (N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (g.generic.coefficients n)) (U : Y.ProEtᵒᵖ)
        (x : ((SemilinearSections.underlying.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj
            ((g.generic.levelPush n).obj N)).obj.obj U),
        HEq (((g.generic.levelPushUnderlying n).hom.app N).hom.app U x) x)
    (δ : ∀ n : ℕ,
      (SpTowerShriek.ev l E X n).obj
          (g.pull.obj (coefficient Y (Arings l E Y))) ⟶
        (SpTowerShriek.ev l E X n).obj (coefficient X (Arings l E X)))
    (hnorm : ∀ (n : ℕ) (U : Y.ProEtᵒᵖ)
        (x : (SpTowerShriek.B l E Y n).obj.obj U)
        (x' : ((SpTowerShriek.ev l E Y n).obj
          (coefficient Y (Arings l E Y))).val.obj U),
        HEq x x' → HEq
          ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv
            _ _) ((g.ordinaryPullEvaluation n).inv.app
              (coefficient Y (Arings l E Y)) ≫ δ n)).val.app U x')
          ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} f CommRingCat.{u + 1}
            (CommRingCat.of.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app
              U x)) :
    ∀ n : ℕ,
        (SemilinearSections.transition (Scheme.ProEt.topology X)
            (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) (Nat.le_succ n)).app
            (g.pull.obj (coefficient Y (Arings l E Y))) ≫
          (SemilinearSections.res (SemilinearSections.coefficientMap
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
            (SpTowerShriek.tau l E X) (Nat.le_succ n))).map (δ n) =
        δ (n + 1) ≫ (SemilinearSections.transition (Scheme.ProEt.topology X)
          (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) (Nat.le_succ n)).app
            (coefficient X (Arings l E X)) := by
  let G := g.generic
  let M := coefficient Y (Arings l E Y)
  obtain ⟨j, hj, ht⟩ := coordinates l E g G.coefficients G.coefficientTransition
    g.coefficients g.transitions G.pull g.pull_eq.symm
    (fun n ↦ ⟨(G.inverseImage n).modules, G.levelPush n, G.levelAdjunction n⟩)
    g.levelAdjunction_eq G.ordinaryPullEvaluation
    (fun n ↦ (g.ordinaryPullEvaluation_eq n).symm)
    (fun n ↦ (G.inverseImage n).moduleUnderlying) G.levelPushUnderlying hpush
    (UnitSuccessorProof.transpose (Scheme.ProEt.topology Y)
      (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) (b.calculus Y)
      (Scheme.ProEt.topology X) _ _ _ G) M
    (fun n ↦ UnitSuccessorProof.horizontal (Scheme.ProEt.topology Y)
      (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) (b.calculus Y)
      (Scheme.ProEt.topology X) _ _ _ G (Nat.le_succ n) M)
  intro n
  apply UnitSuccessorProof.square_of_underlying.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) (Nat.le_succ n)
    (g.pull.obj M) (coefficient X (Arings l E X)) (δ n) (δ (n + 1))
  have ha := normalized_naturality l E (fun k ↦
    ((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E k) f).homEquiv _ _)
      ((g.ordinaryPullEvaluation k).inv.app M ≫ δ k)) hnorm n
  rw [ht n _ (δ n), ht (n + 1) _ (δ (n + 1))] at ha
  exact UnitSuccessorProof.square_of_transposes
    (Scheme.proEtaleSheafAdjunction f (Type (u + 1))) (j n) (j (n + 1))
    _ _ _ _ _ (hj n) ha

end AlgebraicGeometry.ProEtale.SpTowerClasses
