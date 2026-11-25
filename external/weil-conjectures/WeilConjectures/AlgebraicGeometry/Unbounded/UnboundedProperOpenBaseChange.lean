/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.AlgebraicGeometry.Derived.DerivedExchangeModuleTermwiseSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Unbounded proper/open BaseChange

Source: Stacks Project, Tags 0F7F.
-/

@[expose] public section

universe u v w vT wT

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] upperStar lowerStar squareUpperStarIso
  openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit Functor.rightDerivedFunctorUnitQ
  Functor.rightDerivedFunctorObjQIso
  Functor.mapDerivedCategoryNatIso

private theorem natTrans_eq_of_kinjective
    {C : Type v} {T : Type vT} [Category.{w} C] [Category.{wT} T] [Abelian C]
    [HasDerivedCategory C] [Abelian.HasKInjectiveResolutions C]
    (F : CochainComplex C ℤ ⥤ T) (G : DerivedCategory C ⥤ T)
    (a b : F ⟶ DerivedCategory.Q ⋙ G)
    (h : ∀ (J : CochainComplex C ℤ) [J.IsKInjective], a.app J = b.app J) : a = b := by
  apply NatTrans.ext
  funext J
  obtain ⟨I, _, j, _, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective J
  apply (cancel_mono (G.map (DerivedCategory.Q.map j))).mp
  erw [← a.naturality, ← b.naturality, h I]

section Normalization

variable {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (R : C₀ ⥤ C₂) (P : C₁ ⥤ C₃) (K : C₀ ⥤ C₁) (E : C₂ ⥤ C₃)
    [R.Additive] [P.Additive] [K.Additive] [E.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]

private noncomputable def unitQNat (F : C₀ ⥤ C₂) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app := F.rightDerivedFunctorUnitQ
  naturality := fun _ _ f ↦ by
    simpa only [Functor.comp_map] using F.rightDerivedFunctorUnitQ_naturality f

-- The representative normalization compares derived units and localization factorizations.
private theorem normalization_of_representatives
    (θ : R ⋙ E ⟶ K ⋙ P)
    (γ : R.rightDerivedFunctor ⋙ E.mapDerivedCategory ⟶
      K.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (hγ : ∀ (J : CochainComplex C₀ ℤ) [J.IsKInjective]
        (I : CochainComplex C₁ ℤ) [I.IsKInjective]
        (ρ : (K.mapHomologicalComplex (.up ℤ)).obj J ⟶ I) [QuasiIso ρ],
        E.mapDerivedCategory.map (R.rightDerivedFunctorObjQIso J).hom ≫
          E.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ (.up ℤ)).app J) ≫
          DerivedCategory.Q.map ((P.mapHomologicalComplex (.up ℤ)).map ρ) =
        γ.app (DerivedCategory.Q.obj J) ≫
          P.rightDerivedFunctor.map
            (K.mapDerivedCategoryFactors.hom.app J ≫ DerivedCategory.Q.map ρ) ≫
          (P.rightDerivedFunctorObjQIso I).hom)
    (J : CochainComplex C₀ ℤ) :
    E.mapDerivedCategory.map (R.rightDerivedFunctorUnitQ J) ≫
        γ.app (DerivedCategory.Q.obj J) =
      E.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ (.up ℤ)).app J) ≫
        P.rightDerivedFunctorUnitQ ((K.mapHomologicalComplex (.up ℤ)).obj J) ≫
        P.rightDerivedFunctor.map (K.mapDerivedCategoryFactors.inv.app J) := by
  let a : R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ E.mapDerivedCategory ⟶
      DerivedCategory.Q ⋙ K.mapDerivedCategory ⋙ P.rightDerivedFunctor :=
    Functor.whiskerRight (unitQNat R) E.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft DerivedCategory.Q γ
  let b : R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ E.mapDerivedCategory ⟶
      DerivedCategory.Q ⋙ K.mapDerivedCategory ⋙ P.rightDerivedFunctor :=
    Functor.whiskerLeft (R.mapHomologicalComplex (.up ℤ)) E.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (NatTrans.mapHomologicalComplex θ (.up ℤ)) DerivedCategory.Q ≫
      Functor.whiskerLeft (K.mapHomologicalComplex (.up ℤ)) (unitQNat P) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight K.mapDerivedCategoryFactors.inv P.rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom
  have hab : a = b := by
    apply natTrans_eq_of_kinjective _ _ a b
    intro L hL
    obtain ⟨I, _, ρ, _, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      ((K.mapHomologicalComplex (.up ℤ)).obj L)
    have hr := hγ L I ρ
    dsimp only [a, b, unitQNat, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    apply (cancel_mono (P.rightDerivedFunctor.map
      (K.mapDerivedCategoryFactors.hom.app L ≫ DerivedCategory.Q.map ρ) ≫
      (P.rightDerivedFunctorObjQIso I).hom)).mp
    rw [Category.assoc, ← hr, R.rightDerivedFunctorUnitQ_eq]
    simp only [← E.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id,
      Functor.map_comp, Category.assoc]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← P.rightDerivedFunctor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    erw [← P.rightDerivedFunctorUnitQ_naturality_assoc ρ,
      P.rightDerivedFunctorUnitQ_eq I]
    simp
  simpa only [a, b, unitQNat, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using congr_app hab J

end Normalization

section ExactComparison

variable {X Y Y' Z : Type v} [Category.{w} X] [Category.{w} Y]
  [Category.{w} Y'] [Category.{w} Z]
    [Abelian X] [Abelian Y] [Abelian Y'] [Abelian Z]
  [HasDerivedCategory X] [HasDerivedCategory Y]
  [HasDerivedCategory Y'] [HasDerivedCategory Z]
  (F : X ⥤ Y) (J : Y ⥤ Z) (F' : X ⥤ Y') (J' : Y' ⥤ Z)
  [F.Additive] [J.Additive] [F'.Additive] [J'.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  (t : F ⋙ J ≅ F' ⋙ J')

private lemma exactComparison_factors (M : CochainComplex X ℤ) :
    (Functor.mapDerivedCategoryCompIso F J ≪≫
        Functor.mapDerivedCategoryNatIso t ≪≫
        (Functor.mapDerivedCategoryCompIso F' J').symm).hom.app (DerivedCategory.Q.obj M) ≫
      D(J').map (F'.mapDerivedCategoryFactors.hom.app M) ≫
      J'.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj M) =
    D(J).map (F.mapDerivedCategoryFactors.hom.app M) ≫
      J.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t.hom (.up ℤ)).app M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors]
  erw [Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [Category.assoc]

private lemma exactComparison_inv_factors (M : CochainComplex X ℤ) :
    J'.mapDerivedCategoryFactors.inv.app ((F'.mapHomologicalComplex (.up ℤ)).obj M) ≫
      D(J').map (F'.mapDerivedCategoryFactors.inv.app M) ≫
      (Functor.mapDerivedCategoryCompIso F J ≪≫
        Functor.mapDerivedCategoryNatIso t ≪≫
        (Functor.mapDerivedCategoryCompIso F' J').symm).inv.app (DerivedCategory.Q.obj M) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t.inv (.up ℤ)).app M) ≫
      J.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
      D(J).map (F.mapDerivedCategoryFactors.inv.app M) := by
  let A := D(J).mapIso (F.mapDerivedCategoryFactors.app M) ≪≫
    J.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj M)
  let A' := D(J').mapIso (F'.mapDerivedCategoryFactors.app M) ≪≫
    J'.mapDerivedCategoryFactors.app ((F'.mapHomologicalComplex (.up ℤ)).obj M)
  let r : (F ⋙ J).mapHomologicalComplex (.up ℤ) ≅
      (F' ⋙ J').mapHomologicalComplex (.up ℤ) := NatIso.mapHomologicalComplex t _
  have hi : ((Functor.mapDerivedCategoryCompIso F J ≪≫
      Functor.mapDerivedCategoryNatIso t ≪≫
      (Functor.mapDerivedCategoryCompIso F' J').symm).app (DerivedCategory.Q.obj M)) ≪≫ A' =
      A ≪≫ DerivedCategory.Q.mapIso (r.app M) := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      A, A', r, NatIso.mapHomologicalComplex, Category.assoc] using
        exactComparison_factors F J F' J' t M
  simpa only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv,
    A, A', r, NatIso.mapHomologicalComplex, Category.assoc] using congrArg Iso.inv hi

end ExactComparison

private lemma compose_three_eq
    {T : Type v} [Category.{w} T]
    {X₀ X₁ X₂ X₃ X₄ X₅ Y₂ Y₃ X₆ X₇ : T}
    (p₁ : X₀ ⟶ X₁) (p₂ : X₁ ⟶ X₂)
    {f₁ : X₂ ⟶ X₃} {f₂ : X₃ ⟶ X₄} {f₃ : X₄ ⟶ X₅}
    {g₁ : X₂ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} {g₃ : Y₃ ⟶ X₅}
    (s₁ : X₅ ⟶ X₆) (s₂ : X₆ ⟶ X₇) {X₈ : T} (s₃ : X₇ ⟶ X₈)
    (h : f₁ ≫ f₂ ≫ f₃ = g₁ ≫ g₂ ≫ g₃) :
    p₁ ≫ p₂ ≫ f₁ ≫ f₂ ≫ f₃ ≫ s₁ ≫ s₂ ≫ s₃ =
      p₁ ≫ p₂ ≫ g₁ ≫ g₂ ≫ g₃ ≫ s₁ ≫ s₂ ≫ s₃ := by
  simpa only [Category.assoc] using
    congrArg (fun t ↦ p₁ ≫ p₂ ≫ t ≫ s₁ ≫ s₂ ≫ s₃) h

section Cube

variable {B C B' C' B₀ C₀ B₀' C₀' : Type v}
  [Category.{w} B] [Category.{w} C] [Category.{w} B'] [Category.{w} C']
  [Category.{w} B₀] [Category.{w} C₀] [Category.{w} B₀'] [Category.{w} C₀']
    [Abelian B] [Abelian C] [Abelian B'] [Abelian C']
  [Abelian B₀] [Abelian C₀] [Abelian B₀'] [Abelian C₀']
  [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory B'] [HasDerivedCategory C']
  [HasDerivedCategory B₀] [HasDerivedCategory C₀]
  [HasDerivedCategory B₀'] [HasDerivedCategory C₀']
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions B']
  [Abelian.HasKInjectiveResolutions B₀] [Abelian.HasKInjectiveResolutions B₀']
  (G : B ⥤ C) (H : B' ⥤ C') (G₀ : B₀ ⥤ C₀) (H₀ : B₀' ⥤ C₀')
  (P : B ⥤ B') (Q : C ⥤ C') (P₀ : B₀ ⥤ B₀') (Q₀ : C₀ ⥤ C₀')
  (U : B ⥤ B₀) (V : C ⥤ C₀) (U' : B' ⥤ B₀') (V' : C' ⥤ C₀')
  [G.Additive] [H.Additive] [G₀.Additive] [H₀.Additive]
  [P.Additive] [Q.Additive] [P₀.Additive] [Q₀.Additive]
  [U.Additive] [V.Additive] [U'.Additive] [V'.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
  [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
  [PreservesFiniteLimits V'] [PreservesFiniteColimits V']

private def normalizes
    {X Y X' Y' : Type v}
    [Category.{w} X] [Category.{w} Y] [Category.{w} X'] [Category.{w} Y']
    [Abelian X] [Abelian Y] [Abelian X'] [Abelian Y']
    [HasDerivedCategory X] [HasDerivedCategory Y]
    [HasDerivedCategory X'] [HasDerivedCategory Y']
    [Abelian.HasKInjectiveResolutions X] [Abelian.HasKInjectiveResolutions X']
    (G : X ⥤ Y) (H : X' ⥤ Y') (P : X ⥤ X') (Q : Y ⥤ Y')
    [G.Additive] [H.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (e : G ⋙ Q ⟶ P ⋙ H)
    (de : R(G) ⋙ D(Q) ⟶ D(P) ⋙ R(H)) : Prop :=
  ∀ M : CochainComplex X ℤ,
    D(Q).map (G.rightDerivedFunctorUnitQ M) ≫ de.app (DerivedCategory.Q.obj M) =
      Q.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e (.up ℤ)).app M) ≫
        H.rightDerivedFunctorUnitQ ((P.mapHomologicalComplex (.up ℤ)).obj M) ≫
        R(H).map (P.mapDerivedCategoryFactors.inv.app M)

-- The cube compares twelve functors and four localization factorizations.
private theorem derived_cube
    (e : G ⋙ Q ⟶ P ⋙ H) (e₀ : G₀ ⋙ Q₀ ⟶ P₀ ⋙ H₀)
    (a : G ⋙ V ⟶ U ⋙ G₀) (b : H ⋙ V' ⟶ U' ⋙ H₀)
    (c : V ⋙ Q₀ ≅ Q ⋙ V') (d : U ⋙ P₀ ≅ P ⋙ U')
    (de : R(G) ⋙ D(Q) ⟶ D(P) ⋙ R(H))
    (de₀ : R(G₀) ⋙ D(Q₀) ⟶ D(P₀) ⋙ R(H₀))
    (da : R(G) ⋙ D(V) ⟶ D(U) ⋙ R(G₀))
    (db : R(H) ⋙ D(V') ⟶ D(U') ⋙ R(H₀))
    (he : normalizes G H P Q e de) (he₀ : normalizes G₀ H₀ P₀ Q₀ e₀ de₀)
    (ha : normalizes G G₀ U V a da) (hb : normalizes H H₀ U' V' b db)
    (h : ∀ F : B, V'.map (e.app F) ≫ b.app (P.obj F) ≫ H₀.map (d.inv.app F) =
      c.inv.app (G.obj F) ≫ Q₀.map (a.app F) ≫ e₀.app (U.obj F))
    (K : DerivedCategory B) :
    D(V').map (de.app K) ≫ db.app (D(P).obj K) ≫
        R(H₀).map ((Functor.mapDerivedCategoryCompIso U P₀ ≪≫
          Functor.mapDerivedCategoryNatIso d ≪≫
          (Functor.mapDerivedCategoryCompIso P U').symm).inv.app K) =
      (Functor.mapDerivedCategoryCompIso V Q₀ ≪≫
        Functor.mapDerivedCategoryNatIso c ≪≫
        (Functor.mapDerivedCategoryCompIso Q V').symm).inv.app (R(G).obj K) ≫
        D(Q₀).map (da.app K) ≫ de₀.app (D(U).obj K) := by
  generalize hdc : (Functor.mapDerivedCategoryCompIso V Q₀ ≪≫
    Functor.mapDerivedCategoryNatIso c ≪≫ (Functor.mapDerivedCategoryCompIso Q V').symm) = dc
  generalize hdd : (Functor.mapDerivedCategoryCompIso U P₀ ≪≫
    Functor.mapDerivedCategoryNatIso d ≪≫ (Functor.mapDerivedCategoryCompIso P U').symm) = dd
  let α : R(G) ⋙ (D(Q) ⋙ D(V')) ⟶ (D(U) ⋙ D(P₀)) ⋙ R(H₀) :=
    Functor.whiskerRight (de) D(V') ≫
    Functor.whiskerLeft D(P) (db) ≫
    Functor.whiskerRight dd.inv R(H₀)
  let β : R(G) ⋙ (D(Q) ⋙ D(V')) ⟶ (D(U) ⋙ D(P₀)) ⋙ R(H₀) :=
    Functor.whiskerLeft R(G) dc.inv ≫
    Functor.whiskerRight (da) D(Q₀) ≫
    Functor.whiskerLeft D(U) (de₀)
  have heqQ (M : CochainComplex B ℤ) :
      D(V').map (D(Q).map (G.rightDerivedFunctorUnitQ M)) ≫
          α.app (DerivedCategory.Q.obj M) =
        D(V').map (D(Q).map (G.rightDerivedFunctorUnitQ M)) ≫
          β.app (DerivedCategory.Q.obj M) := by
    simp (config := { zeta := false }) only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    rw [← D(V').map_comp_assoc, he M]
    have hc := dc.inv.naturality (G.rightDerivedFunctorUnitQ M)
    simp (config := { zeta := false }) only [Functor.comp_map] at hc
    rw [reassoc_of% hc, ← D(Q₀).map_comp_assoc, ha M]
    simp (config := { zeta := false }) only [Functor.map_comp, Category.assoc]
    -- Move the localization comparisons through the remaining faces and factor them.
    have hbn := db.naturality
      (P.mapDerivedCategoryFactors.inv.app M)
    have hen := de₀.naturality
      (U.mapDerivedCategoryFactors.inv.app M)
    simp (config := { zeta := false }) only [Functor.comp_map, Functor.comp_obj] at hbn hen
    rw [reassoc_of% hbn, hen]
    rw [reassoc_of% hb (P.mapHomologicalComplex (.up ℤ) |>.obj M),
      reassoc_of% he₀ (U.mapHomologicalComplex (.up ℤ) |>.obj M)]
    have hv := V'.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex e (.up ℤ)).app M)
    have hq := Q₀.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex a (.up ℤ)).app M)
    simp (config := { zeta := false }) only [Functor.comp_map, Functor.comp_obj] at hv hq
    change D(V').map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex e (.up ℤ)).app M)) ≫
      V'.mapDerivedCategoryFactors.hom.app
        ((H.mapHomologicalComplex (.up ℤ)).obj ((P.mapHomologicalComplex (.up ℤ)).obj M)) =
      _ at hv
    change D(Q₀).map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex a (.up ℤ)).app M)) ≫
      Q₀.mapDerivedCategoryFactors.hom.app
        ((G₀.mapHomologicalComplex (.up ℤ)).obj ((U.mapHomologicalComplex (.up ℤ)).obj M)) =
      _ at hq
    rw [reassoc_of% hv, reassoc_of% hq]
    -- Express the two exact edges by their termwise comparisons.
    have hd := exactComparison_inv_factors U P₀ P U' d M
    rw [hdd] at hd
    rw [← R(H₀).map_comp_assoc
      (U'.mapDerivedCategoryFactors.inv.app ((P.mapHomologicalComplex (.up ℤ)).obj M))
      (D(U').map (P.mapDerivedCategoryFactors.inv.app M))]
    rw [← R(H₀).map_comp
      (U'.mapDerivedCategoryFactors.inv.app ((P.mapHomologicalComplex (.up ℤ)).obj M) ≫
        D(U').map (P.mapDerivedCategoryFactors.inv.app M))
      (dd.inv.app (DerivedCategory.Q.obj M))]
    rw [Category.assoc, hd]
    simp (config := { zeta := false }) only [Functor.map_comp]
    have hn := H₀.rightDerivedFunctorUnitQ_naturality
      ((NatTrans.mapHomologicalComplex d.inv (.up ℤ)).app M)
    change DerivedCategory.Q.map ((H₀.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex d.inv (.up ℤ)).app M)) ≫
      H₀.rightDerivedFunctorUnitQ
        ((P₀.mapHomologicalComplex (.up ℤ)).obj ((U.mapHomologicalComplex (.up ℤ)).obj M)) =
      H₀.rightDerivedFunctorUnitQ
        ((U'.mapHomologicalComplex (.up ℤ)).obj ((P.mapHomologicalComplex (.up ℤ)).obj M)) ≫
      R(H₀).map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex d.inv (.up ℤ)).app M)) at hn
    rw [← reassoc_of% hn]
    have hcf := exactComparison_factors V Q₀ Q V' c ((G.mapHomologicalComplex (.up ℤ)).obj M)
    rw [hdc] at hcf
    have hci : dc.inv.app (DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj M)) ≫
        D(Q₀).map (V.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj M)) ≫
        Q₀.mapDerivedCategoryFactors.hom.app
          ((V.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj M)) =
      D(V').map (Q.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj M)) ≫
        V'.mapDerivedCategoryFactors.hom.app
          ((Q.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj M)) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.inv (.up ℤ)).app
          ((G.mapHomologicalComplex (.up ℤ)).obj M)) := by
      apply (cancel_epi (dc.hom.app
        (DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj M)))).1
      simp (config := { zeta := false }) only
        [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      rw [Category.assoc, Category.assoc, reassoc_of% hcf]
      simp (config := { zeta := false }) only [← DerivedCategory.Q.map_comp,
        ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
        Iso.hom_inv_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
    change dc.inv.app (DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj M)) ≫
      D(Q₀).map (V.mapDerivedCategoryFactors.hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj M)) ≫
      Q₀.mapDerivedCategoryFactors.hom.app (((G ⋙ V).mapHomologicalComplex (.up ℤ)).obj M) =
      D(V').map (Q.mapDerivedCategoryFactors.hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj M)) ≫
      V'.mapDerivedCategoryFactors.hom.app (((G ⋙ Q).mapHomologicalComplex (.up ℤ)).obj M) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.inv (.up ℤ)).app
        ((G.mapHomologicalComplex (.up ℤ)).obj M)) at hci
    rw [reassoc_of% hci]
    -- The resulting termwise composites are equal by the underived cube hypothesis.
    let l : G ⋙ Q ⋙ V' ⟶ (U ⋙ P₀) ⋙ H₀ :=
      Functor.whiskerRight e V' ≫ Functor.whiskerLeft P b ≫ Functor.whiskerRight d.inv H₀
    let r : G ⋙ Q ⋙ V' ⟶ (U ⋙ P₀) ⋙ H₀ :=
      Functor.whiskerLeft G c.inv ≫ Functor.whiskerRight a Q₀ ≫ Functor.whiskerLeft U e₀
    have hlr : l = r := by
      apply NatTrans.ext
      funext F
      exact h F
    have hh : (V'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex e (.up ℤ)).app M) ≫
          (NatTrans.mapHomologicalComplex b (.up ℤ)).app
            ((P.mapHomologicalComplex (.up ℤ)).obj M) ≫
          (H₀.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex d.inv (.up ℤ)).app M) =
        (NatTrans.mapHomologicalComplex c.inv (.up ℤ)).app
            ((G.mapHomologicalComplex (.up ℤ)).obj M) ≫
          (Q₀.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex a (.up ℤ)).app M) ≫
          (NatTrans.mapHomologicalComplex e₀ (.up ℤ)).app
            ((U.mapHomologicalComplex (.up ℤ)).obj M) := by
      ext n
      exact congr_app hlr (M.X n)
    have hqh := congrArg DerivedCategory.Q.map hh
    simp (config := { zeta := false }) only [Functor.map_comp] at hqh
    exact compose_three_eq
      (D(V').map (Q.mapDerivedCategoryFactors.hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj M)))
      (V'.mapDerivedCategoryFactors.hom.app
        (((G ⋙ Q).mapHomologicalComplex (.up ℤ)).obj M))
      (H₀.rightDerivedFunctorUnitQ
        ((P₀.mapHomologicalComplex (.up ℤ)).obj ((U.mapHomologicalComplex (.up ℤ)).obj M)))
      (R(H₀).map (P₀.mapDerivedCategoryFactors.inv.app
        ((U.mapHomologicalComplex (.up ℤ)).obj M)))
      (R(H₀).map (D(P₀).map (U.mapDerivedCategoryFactors.inv.app M))) hqh
  have heq : α = β := by
    apply NatTrans.ext
    funext L
    obtain ⟨I, hI, ⟨s⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective L
    have := hI
    have hunit : IsIso (G.rightDerivedFunctorUnitQ I) := by
      rw [G.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have hi : α.app (DerivedCategory.Q.obj I) = β.app (DerivedCategory.Q.obj I) :=
      (cancel_epi (D(V').map (D(Q).map (G.rightDerivedFunctorUnitQ I)))).mp (heqQ I)
    apply (cancel_mono (((D(U) ⋙ D(P₀)) ⋙ R(H₀)).map s.hom)).mp
    rw [← α.naturality, ← β.naturality, hi]
  simpa only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] using congr_app heq K

end Cube

private theorem baseChange_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z X' Y' Z' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : Z' ⟶ Z)
    (sqf : CommSq a f' f b) (sqg : CommSq b g' g c)
    (h : X ⟶ Z) (hh : h = f ≫ g) (h' : X' ⟶ Z') (hh' : h' = f' ≫ g')
    (sq : CommSq a h' h c) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (c)^*[ModuleCat.{u + 1} A].map
        ((lowerStarComp (ModuleCat.{u + 1} A) f g h hh).hom.app F) ≫
        (baseChangeMap (ModuleCat.{u + 1} A) sq).app F =
      (baseChangeMap (ModuleCat.{u + 1} A) sqg).app
          ((f)_*[ModuleCat.{u + 1} A].obj F) ≫
        (g')_*[ModuleCat.{u + 1} A].map
          ((baseChangeMap (ModuleCat.{u + 1} A) sqf).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) f' g' h' hh').hom.app
          ((a)^*[ModuleCat.{u + 1} A].obj F) := by
  subst h
  subst h'
  rw [baseChangeMap_paste_vert_app (ModuleCat.{u + 1} A) sqf sqg sq]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem exchange_normalization (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) :
    normalizes (f)_*[ModuleCat.{u + 1} A] (f')_*[ModuleCat.{u + 1} A]
      (g')^*[ModuleCat.{u + 1} A] (g)^*[ModuleCat.{u + 1} A]
      (baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq)
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq) := by
  intro I
  exact derivedExchangeUnitQ
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f')
    (squareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq) I

-- The support cube contains eight sheaf functors and both direct-image compositors.
private theorem ordinary_cube (A : Type (u + 1)) [CommRing A]
    (θ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
          (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (hθ : (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (θ k r p i sq).hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F))
    {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    [IsNoetherian U₁] [IsNoetherian V₁] [IsNoetherian W₁] [IsNoetherian Z₁]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (k₁ : U₁ ⟶ V₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁) (i₁ : W₁ ⟶ Z₁)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
    (sq : CommSq k r p i) (sq₁ : CommSq k₁ r₁ p₁ i₁)
    (a : V₁ ⟶ V) (b : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
    (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c)
    (si : IsPullback c i₁ i b) (sk : IsPullback d k₁ k a)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (b)^*[ModuleCat.{u + 1} A].map ((θ k r p i sq).hom.app F) ≫
        (baseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq).app
          ((k)_!open[ModuleCat.{u + 1} A].obj F) ≫
        (p₁)_*[ModuleCat.{u + 1} A].map
          ((@asIso _ _ _ _ _
            (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sk)).inv.app F) =
      (@asIso _ _ _ _ _
          (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) si)).inv.app
            ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
        (i₁)_!open[ModuleCat.{u + 1} A].map
          ((baseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq).app F) ≫
        (θ k₁ r₁ p₁ i₁ sq₁).hom.app ((d)^*[ModuleCat.{u + 1} A].obj F) := by
  let bk := @asIso _ _ _ _ _
    (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sk)
  let bi := @asIso _ _ _ _ _
    (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) si)
  have hk M : bk.inv.app M ≫
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k₁).app
        ((d)^*[ModuleCat.{u + 1} A].obj M) =
      (a)^*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app M) ≫
        (baseChangeMap (ModuleCat.{u + 1} A) sk.toCommSq).app M := by
    apply (cancel_epi (bk.hom.app M)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    exact (openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app
      (ModuleCat.{u + 1} A) sk.toCommSq M).symm
  have hi M : bi.inv.app M ≫
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i₁).app
        ((c)^*[ModuleCat.{u + 1} A].obj M) =
      (b)^*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app M) ≫
        (baseChangeMap (ModuleCat.{u + 1} A) si.toCommSq).app M := by
    apply (cancel_epi (bi.hom.app M)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    exact (openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app
      (ModuleCat.{u + 1} A) si.toCommSq M).symm
  have := mono_openImmersionLowerShriekToLowerStar_app A k₁ ((d)^*[ModuleCat.{u + 1} A].obj F)
  apply (cancel_mono ((p₁)_*[ModuleCat.{u + 1} A].map
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k₁).app
      ((d)^*[ModuleCat.{u + 1} A].obj F)) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) k₁ p₁).hom.app
        ((d)^*[ModuleCat.{u + 1} A].obj F))).mp
  simp only [Category.assoc]
  rw [← (p₁)_*[ModuleCat.{u + 1} A].map_comp_assoc, hk]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := (baseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq).naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  have s : CommSq d (k₁ ≫ p₁) (k ≫ p) b := ⟨by
    rw [← Category.assoc, sk.w, Category.assoc, sp.w, Category.assoc]⟩
  rw [← baseChange_comp A k p k₁ p₁ d a b sk.toCommSq sp.toCommSq
    (k ≫ p) rfl (k₁ ≫ p₁) rfl s F]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [hθ]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [baseChange_comp A r i r₁ i₁ d c b sr.toCommSq si.toCommSq
    (k ≫ p) sq.w (k₁ ≫ p₁) sq₁.w s F]
  rw [← reassoc_of% hi]
  rw [← reassoc_of% (openImmersionLowerShriekToLowerStar
    (ModuleCat.{u + 1} A) i₁).naturality
      ((baseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq).app F)]
  rw [hθ k₁ r₁ p₁ i₁ sq₁]

private theorem derived_open_comparison
    (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {j' : X' ⟶ Y'} {j : X ⟶ Y} {g : Y' ⟶ Y}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback g' j' j g) :
    mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) sq =
      Functor.mapDerivedCategoryCompIso (g')^*[ModuleCat.{u + 1} A]
        (j')_!open[ModuleCat.{u + 1} A] ≪≫
      Functor.mapDerivedCategoryNatIso
        (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
          (ModuleCat.{u + 1} A) sq)) ≪≫
      (Functor.mapDerivedCategoryCompIso (j)_!open[ModuleCat.{u + 1} A]
        (g)^*[ModuleCat.{u + 1} A]).symm := by
  rfl

-- Elaborating the specialization compares the eight sheaf categories of the cube.
/-- BaseChange for families normalized on sheaves and on every K-injective representative.
Source: Stacks Project, Tags 0F7F.
(blueprint: lem-amb-unbounded-proper-open-base-change).

Proof:
Extend the representative normalization to a right-derived unit identity on every complex.
Both sides form natural transformations; they agree on K-injective complexes by resolving
k!J and using naturality of the derived unit, and equality extends to all complexes by a
K-injective resolution. The exact adjunction-mate factorization gives the same unit identity
for the specified unbounded exchange. Prove the ordinary sheaf cube by including both paths
in the common direct image: the open comparison is monic, its base-change identity moves it
through the open faces, and mate pasting and support normalization identify the two paths.
For the derived cube, precompose its two paths on Q(M) by the twice-exact image of the derived
unit. Naturality, the four unit identities, and the exact comparison factorizations reduce
the equality to the degreewise ordinary cube. For K-injective M the precomposed unit is an
isomorphism, so cancel it; naturality transports the equality to every derived object.
No exchange map is cancelled and inverse image need not preserve K-injectives.
-/
theorem unboundedProperOpenBaseChange_of_normalization (A : Type (u + 1)) [CommRing A] [Finite A]
    (θ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
          (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (Γ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
          D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]))
    (hθ : (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (θ k r p i sq).hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F))
    (hΓ : (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [J.IsKInjective]
        (I : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective]
        (ρ : ((k)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso ρ],
        D((i)_!open[ModuleCat.{u + 1} A]).map
            (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso J).hom ≫
          ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
            (((r)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (θ k r p i sq).hom (.up ℤ)).app J) ≫
          DerivedCategory.Q.map
            (((p)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).map ρ) =
        (Γ k r p i sq).hom.app (DerivedCategory.Q.obj J) ≫
          R((p)_*[ModuleCat.{u + 1} A]).map
            (((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
              DerivedCategory.Q.map ρ) ≫
          (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom)) :
    (∀ {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        [IsNoetherian U₁] [IsNoetherian V₁] [IsNoetherian W₁] [IsNoetherian Z₁]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        (k₁ : U₁ ⟶ V₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁) (i₁ : W₁ ⟶ Z₁)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
        (sq : CommSq k r p i) (sq₁ : CommSq k₁ r₁ p₁ i₁)
        (a : V₁ ⟶ V) (b : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
        (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c)
        (si : IsPullback c i₁ i b) (sk : IsPullback d k₁ k a)
        (K : DerivedCategoryModule A U),
        D((b)^*[ModuleCat.{u + 1} A]).map ((Γ k r p i sq).hom.app K) ≫
            (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq).app
              (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
            R((p₁)_*[ModuleCat.{u + 1} A]).map
              ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
                (ModuleCat.{u + 1} A) sk).inv.app K) =
          (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
              (ModuleCat.{u + 1} A) si).inv.app
                (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            D((i₁)_!open[ModuleCat.{u + 1} A]).map
              ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq).app K) ≫
            (Γ k₁ r₁ p₁ i₁ sq₁).hom.app (D((d)^*[ModuleCat.{u + 1} A]).obj K)) := by
  intro U V W Z U₁ V₁ W₁ Z₁ _ _ _ _ _ _ _ _
    k r p i k₁ r₁ p₁ i₁ _ _ _ _ _ _ _ _ sq sq₁ a b c d sp sr si sk K
  rw [derived_open_comparison A sk, derived_open_comparison A si]
  exact derived_cube
    (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
    (r₁)_*[ModuleCat.{u + 1} A] (p₁)_*[ModuleCat.{u + 1} A]
    (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A]
    (k₁)_!open[ModuleCat.{u + 1} A] (i₁)_!open[ModuleCat.{u + 1} A]
    (d)^*[ModuleCat.{u + 1} A] (c)^*[ModuleCat.{u + 1} A]
    (a)^*[ModuleCat.{u + 1} A] (b)^*[ModuleCat.{u + 1} A]
    (θ k r p i sq).hom (θ k₁ r₁ p₁ i₁ sq₁).hom
    (baseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq)
    (baseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq)
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} A) si))
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} A) sk))
    (Γ k r p i sq).hom (Γ k₁ r₁ p₁ i₁ sq₁).hom
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq)
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq)
    (normalization_of_representatives _ _ _ _ _ _ (hΓ k r p i sq))
    (normalization_of_representatives _ _ _ _ _ _ (hΓ k₁ r₁ p₁ i₁ sq₁))
    (exchange_normalization A sr) (exchange_normalization A sp)
    (ordinary_cube A θ hθ k r p i k₁ r₁ p₁ i₁ sq sq₁ a b c d sp sr si sk) K

end AlgebraicGeometry.Etale
