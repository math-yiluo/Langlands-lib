/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData

/-! # Evaluation of the normalized tower adjunction

Source: blueprint latest, integral direct-image proof, paragraph (3), and the
specified unit and counit evaluation laws of the semilinear section calculus.
(blueprint: lem-sp-tower-geometry-adjunction-evaluation)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem derived_package_eq
    {C₀ C₁ : Type*} [Category C₀] [Category C₁] [Abelian C₀] [Abelian C₁]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [Abelian.HasKInjectiveResolutions C₁]
    {L L' : C₀ ⥤ C₁} {P P' : C₁ ⥤ C₀}
    [L.Additive] [L'.Additive] [P.Additive] [P'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    (a : L ⊣ P) (a' : L' ⊣ P')
    (h : (⟨L, P, a⟩ : Σ F : C₀ ⥤ C₁, Σ G : C₁ ⥤ C₀, F ⊣ G) = ⟨L', P', a'⟩) :
    (⟨L.mapDerivedCategory, P.rightDerivedFunctor,
      a.mapDerivedCategoryRightDerivedAdjunction⟩ :
      Σ F : DerivedCategory C₀ ⥤ DerivedCategory C₁,
      Σ G : DerivedCategory C₁ ⥤ DerivedCategory C₀, F ⊣ G) =
    ⟨L'.mapDerivedCategory, P'.rightDerivedFunctor,
      a'.mapDerivedCategoryRightDerivedAdjunction⟩ := by
  have hL : L = L' := congrArg Sigma.fst h
  subst L'
  have hP : P = P' := congrArg (fun z ↦ z.2.1) h
  subst P'
  have ha : a = a' := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, eq_self, true_and] using h
  subst a'
  rfl

private theorem evaluation_coordinates
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    (e₀ : C₀ ⥤ D₀) (e₁ : C₁ ⥤ D₁)
    {L : C₀ ⥤ C₁} {P : C₁ ⥤ C₀} (a a' : L ⊣ P)
    {L₀ L₁ : D₀ ⥤ D₁} {P₀ P₁ : D₁ ⥤ D₀}
    (s : L₀ ⊣ P₀) (s' : L₁ ⊣ P₁)
    (hs : (⟨L₀, P₀, s⟩ : Σ F : D₀ ⥤ D₁, Σ G : D₁ ⥤ D₀, F ⊣ G) = ⟨L₁, P₁, s'⟩)
    (p : L ⋙ e₁ ≅ e₀ ⋙ L₁) (q : P ⋙ e₀ ≅ e₁ ⋙ P₁)
    (p' : L ⋙ e₁ ≅ e₀ ⋙ L₀) (q' : P ⋙ e₀ ≅ e₁ ⋙ P₀)
    (hp : HEq p p') (hq : HEq q q') (ha : a = a')
    (hu : ∀ M : C₀, e₀.map (a'.unit.app M) ≫ q'.hom.app (L.obj M) ≫
      P₀.map (p'.hom.app M) = s.unit.app (e₀.obj M))
    (hc : ∀ N : C₁, L₀.map (q'.hom.app N) ≫ s.counit.app (e₁.obj N) =
      p'.inv.app (P.obj N) ≫ e₁.map (a'.counit.app N)) :
    (∀ M : C₀, e₀.map (a.unit.app M) ≫ q.hom.app (L.obj M) ≫
      P₁.map (p.hom.app M) = s'.unit.app (e₀.obj M)) ∧
    (∀ N : C₁, L₁.map (q.hom.app N) ≫ s'.counit.app (e₁.obj N) =
      p.inv.app (P.obj N) ≫ e₁.map (a.counit.app N)) := by
  have hL : L₀ = L₁ := congrArg Sigma.fst hs
  subst L₁
  have hP : P₀ = P₁ := congrArg (fun z ↦ z.2.1) hs
  subst P₁
  have hs' : s = s' := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, eq_self, true_and] using hs
  subst s'
  have hp' : p = p' := eq_of_heq hp
  have hq' : q = q' := eq_of_heq hq
  subst p
  subst q
  subst a'
  exact ⟨hu, hc⟩

private theorem geometry_evaluation_transport (b : Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (n : ℕ)
    (C : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τC : ∀ m : ℕ, C (m + 1) ⟶ C m)
    (Pg : S l E Y ⥤ WeilConjectures.SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) C τC)
    (Qg : WeilConjectures.SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) C τC ⥤ S l E Y)
    [Pg.Additive] [PreservesFiniteLimits Pg] [PreservesFiniteColimits Pg] [Qg.Additive]
    [Abelian.HasKInjectiveResolutions
      (WeilConjectures.SemilinearSections.Systems.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) C τC)]
    (Ad : Pg.mapDerivedCategory ⊣ Qg.rightDerivedFunctor)
    (Ln : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (B l E Y n) ⥤
      WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (C n))
    (Rn : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (C n) ⥤
      WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (B l E Y n))
    [Ln.Additive] [PreservesFiniteLimits Ln] [PreservesFiniteColimits Ln] [Rn.Additive]
    [Abelian.HasKInjectiveResolutions
      (WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (C n))]
    (An : Ln ⊣ Rn) (AnD : Ln.mapDerivedCategory ⊣ Rn.rightDerivedFunctor)
    (hAnD : AnD = An.mapDerivedCategoryRightDerivedAdjunction)
    (pg : Pg.mapDerivedCategory ⋙
      WeilConjectures.SemilinearSections.e.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) C τC n ≅ Ev l E Y n ⋙ Ln.mapDerivedCategory)
    (qg : Qg.rightDerivedFunctor ⋙ Ev l E Y n ≅
      WeilConjectures.SemilinearSections.e.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) C τC n ⋙ Rn.rightDerivedFunctor)
    (hu : ∀ M : D l E Y, (Ev l E Y n).map (Ad.unit.app M) ≫
      qg.hom.app (Pg.mapDerivedCategory.obj M) ≫
        Rn.rightDerivedFunctor.map (pg.hom.app M) = AnD.unit.app ((Ev l E Y n).obj M))
    (hc : ∀ N, Ln.mapDerivedCategory.map (qg.hom.app N) ≫
      AnD.counit.app ((WeilConjectures.SemilinearSections.e.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) C τC n).obj N) =
      pg.inv.app (Qg.rightDerivedFunctor.obj N) ≫
        (WeilConjectures.SemilinearSections.e.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) C τC n).map (Ad.counit.app N))
    (P : S l E Y ⥤ S l E X) (Q : S l E X ⥤ S l E Y)
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P] [Q.Additive]
    (A : P ⊣ Q)
    (p : P.mapDerivedCategory ⋙ Ev l E X n ≅
      Ev l E Y n ⋙ proEtaleConstantRingDerivedPullback (R l E n) f)
    (q : Q.rightDerivedFunctor ⋙ Ev l E Y n ≅
      Ev l E X n ⋙ (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor)
    (hC : C = B l E X) (ht : HEq τC (tau l E X))
    (hP : HEq P Pg) (hQ : HEq Q Qg)
    (hdA : HEq A.mapDerivedCategoryRightDerivedAdjunction Ad)
    (hp : HEq p pg) (hq : HEq q qg)
    (hAn : HEq
      (⟨Ln, Rn, An⟩ :
        Σ L : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (C n),
        Σ R : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (C n) ⥤
          WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ R)
      (⟨proEtaleConstantRingPullback (R l E n) f,
        proEtaleConstantRingPushforward (R l E n) f,
        proEtaleConstantRingAdjunction (R l E n) f⟩ :
        Σ L : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n),
        Σ R : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n) ⥤
          WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ R)) :
    (∀ M : D l E Y,
      (Ev l E Y n).map (A.mapDerivedCategoryRightDerivedAdjunction.unit.app M) ≫
        q.hom.app (P.mapDerivedCategory.obj M) ≫
        (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor.map
          (p.hom.app M) =
      (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction.unit.app
        ((Ev l E Y n).obj M)) ∧
    (∀ N : D l E X,
      (proEtaleConstantRingDerivedPullback (R l E n) f).map (q.hom.app N) ≫
        (Adjunction.counit
          (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction).app
          ((Ev l E X n).obj N) =
      p.inv.app (Q.rightDerivedFunctor.obj N) ≫
        (Ev l E X n).map (A.mapDerivedCategoryRightDerivedAdjunction.counit.app N)) := by
  subst C
  have ht' : τC = tau l E X := eq_of_heq ht
  subst τC
  have hP' : P = Pg := eq_of_heq hP
  subst P
  have hQ' : Q = Qg := eq_of_heq hQ
  subst Q
  have hdA' : A.mapDerivedCategoryRightDerivedAdjunction = Ad := eq_of_heq hdA
  have hs := derived_package_eq An (proEtaleConstantRingAdjunction (R l E n) f)
    (eq_of_heq hAn)
  rw [← hAnD] at hs
  exact evaluation_coordinates (Ev l E Y n) (Ev l E X n)
    A.mapDerivedCategoryRightDerivedAdjunction Ad AnD
    (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction
    hs p q pg qg hp hq hdA' hu hc

/-- The concrete section-model comparisons preserve the derived adjunction unit
and counit. This involves no tensor, compactification, or constructibility test.
Source: blueprint latest, integral direct-image proof, paragraph (3), evaluation of
projection transposes; SemilinearSections.Geometry.unit_evaluation and
counit_evaluation (blueprint: lem-sp-tower-geometry-adjunction-evaluation).
Proof: transport the generic unit and counit evaluation equations through the
coefficient, transition, target, pull and push identifications of Geometry. Its
specified pullEvaluation and pushEvaluation are the generic comparisons, and
its derivedAdjunction_eq and levelAdjunction_eq identify both adjunctions with
their canonical ordinary-derived localizations. Thus the transported equations
are precisely the two displayed equations. No detection of equality by levels is used. -/
theorem geometry_adjunction_evaluation (b : Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : Geometry l E b f) (n : ℕ) :
    (∀ M : D l E Y,
      (Ev l E Y n).map ((adjunction l E b g).unit.app M) ≫
        (g.pushEvaluation n).hom.app ((pull l E b g).obj M) ≫
        (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor.map
          ((g.pullEvaluation n).hom.app M) =
      (Adjunction.unit
        (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction).app
        ((Ev l E Y n).obj M)) ∧
    (∀ N : D l E X,
      (proEtaleConstantRingDerivedPullback (R l E n) f).map
          ((g.pushEvaluation n).hom.app N) ≫
        (Adjunction.counit
          (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction).app
          ((Ev l E X n).obj N) =
      (g.pullEvaluation n).inv.app ((push l E b g).obj N) ≫
        (Ev l E X n).map ((adjunction l E b g).counit.app N)) := by
  exact geometry_evaluation_transport l E b n
    g.generic.coefficients g.generic.coefficientTransition g.generic.pull g.generic.push
    g.generic.adjunction (g.generic.inverseImage n).modules (g.generic.levelPush n)
    (g.generic.levelAdjunction n) (g.generic.derivedLevelAdjunction n)
    (g.generic.derivedLevelAdjunction_canonical n)
    (g.generic.pullEvaluation n) (g.generic.pushEvaluation n)
    (g.generic.unit_evaluation n) (g.generic.counit_evaluation n)
    g.pull g.push g.ordinaryAdjunction (g.pullEvaluation n) (g.pushEvaluation n)
    g.coefficients g.transitions g.pull_eq g.push_eq g.derivedAdjunction_eq
    (g.pullEvaluation_eq n) (g.pushEvaluation_eq n) (g.levelAdjunction_eq n)

end AlgebraicGeometry.ProEtale.SpTowerShriek
