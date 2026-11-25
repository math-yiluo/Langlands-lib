/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorAcyclic
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.KFlatTensorConeTwoOutOfThree
public import WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenCartesianNormalization
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenCubeNormalization
import all WeilConjectures.AlgebraicGeometry.UnboundedProperOpenComposition
import all WeilConjectures.AlgebraicGeometry.UnboundedProperOpenInterchange
import all WeilConjectures.AlgebraicGeometry.UnboundedProperOpenPasting

/-! # Normalized unbounded proper/open interchange and its base-change cube

Source: Stacks Project, more-etale.tex, Tags 0F7B(b), 0F7C, 0F7D, 0F7E and 0F7F.
(auxiliary; not a blueprint node).

The comparison families below use the ordinary unbounded module derived categories.
The sheaf comparison is fixed by equality inside the common ordinary direct image;
the derived comparison is fixed on every K-injective representative and resolution.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive
attribute [local irreducible] lowerStar openImmersionLowerShriek Functor.mapDerivedCategory
  Functor.rightDerivedFunctor
attribute [local irreducible] Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh Functor.rightDerivedFunctorUnit
  Functor.rightDerivedFunctorObjQIso Functor.mapDerivedCategoryNatIso

/-- The type of sheaf comparisons for proper vertical and open horizontal edges.
Source: Stacks Project, Tag 0F7B, first proof paragraph
(auxiliary; not a blueprint node). -/
abbrev ProperOpenSheafComparisonFamily (A : Type (u + 1)) [CommRing A] :=
  ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k],
    CommSq k r p i →
      ((r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
        (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])

/-- The type of unbounded derived proper/open comparison families.
Source: Stacks Project, Tag 0F7B(b)
(auxiliary; not a blueprint node). -/
abbrev ProperOpenDerivedComparisonFamily (A : Type (u + 1)) [CommRing A] :=
  ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k],
    CommSq k r p i →
      (R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
        D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]))

private theorem identity_leftAdjoint_compare
    {C : Type*} [Category C] {F G : C ⥤ C} (adj : F ⊣ G) (e : G ≅ 𝟭 C) :
    adj.leftAdjointUniq (Adjunction.id.ofNatIsoRight e.symm) =
      Adjunction.leftAdjointIdIso adj e := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (adj.homEquiv X X).injective
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp [Adjunction.leftAdjointIdIso, conjugateIsoEquiv,
    Adjunction.homEquiv_unit, Adjunction.ofNatIsoRight_unit]

set_option backward.isDefEq.respectTransparency false in
private theorem rearrange_representative
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {A B C' D' E : D}
    (u : A ≅ B) (v : B ≅ C') (e : X ≅ Y) (r : Y ≅ Z) (f : F.obj Z ≅ E)
    (c : C' ⟶ D') (d : D' ⟶ E) (g : A ⟶ F.obj X)
    (h : u.hom ≫ v.hom ≫ c ≫ d = g ≫ F.map (e.hom ≫ r.hom) ≫ f.hom) :
    v.inv ≫ u.inv ≫ g = c ≫ d ≫ f.inv ≫ F.map (r.inv ≫ e.inv) := by
  let w := F.mapIso (e ≪≫ r) ≪≫ f
  have hh := congrArg (fun t => (u ≪≫ v).inv ≫ t ≫ w.inv) h
  simpa [w, Functor.map_comp, Category.assoc] using hh.symm

private theorem normalized_unit
    {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (R : C₀ ⥤ C₂) (P : C₁ ⥤ C₃) (K : C₀ ⥤ C₁) (E : C₂ ⥤ C₃)
    [R.Additive] [P.Additive] [K.Additive] [E.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (θ : R ⋙ E ≅ K ⋙ P)
    (N : NormalizedDerivedComparison R P K E θ) :
    ProperOpenUnitNormalized R P K E θ.hom N.comparison.hom := by
  exact N.unit_normalization

private theorem representative_inverse_formula
    {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (R : C₀ ⥤ C₂) (P : C₁ ⥤ C₃) (K : C₀ ⥤ C₁) (E : C₂ ⥤ C₃)
    [R.Additive] [P.Additive] [K.Additive] [E.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (θ : R ⋙ E ≅ K ⋙ P)
    (Γ : R.rightDerivedFunctor ⋙ E.mapDerivedCategory ≅
      K.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (hΓ : ProperOpenUnitNormalized R P K E θ.hom Γ.hom)
    (I : CochainComplex C₀ ℤ) [I.IsKInjective]
    (H : CochainComplex C₁ ℤ) [H.IsKInjective]
    (ρ : (K.mapHomologicalComplex (.up ℤ)).obj I ⟶ H) [QuasiIso ρ] :
    E.mapDerivedCategoryFactors.inv.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
        E.mapDerivedCategory.map (R.rightDerivedFunctorObjQIso I).inv ≫
        Γ.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app I ≫
            (P.mapHomologicalComplex (.up ℤ)).map ρ) ≫
        (P.rightDerivedFunctorObjQIso H).inv ≫
        P.rightDerivedFunctor.map
          (inv (DerivedCategory.Q.map ρ) ≫ K.mapDerivedCategoryFactors.inv.app I) := by
  erw [DerivedCategory.Q.map_comp]
  dsimp only [Functor.comp_obj]
  simpa only [Category.assoc, Functor.mapIso_inv, Iso.app_inv, asIso_inv,
    Functor.comp_obj] using
    rearrange_representative P.rightDerivedFunctor
      (E.mapDerivedCategory.mapIso (R.rightDerivedFunctorObjQIso I))
      (E.mapDerivedCategoryFactors.app ((R.mapHomologicalComplex (.up ℤ)).obj I))
      (K.mapDerivedCategoryFactors.app I) (asIso (DerivedCategory.Q.map ρ))
      (P.rightDerivedFunctorObjQIso H) _ _ _ (comparison_representative R P K E θ Γ I H ρ
        (hΓ ((HomotopyCategory.quotient _ _).obj I)))

set_option backward.isDefEq.respectTransparency false in
@[irreducible] private noncomputable def chosen_sheaf_family
    (A : Type (u + 1)) [CommRing A] : ProperOpenSheafComparisonFamily A :=
  fun k r p i _ _ _ _ sq => (exists_sheafComparison A k r p i sq).choose

set_option backward.isDefEq.respectTransparency false in
@[irreducible] private noncomputable def chosen_normalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (θ : ProperOpenSheafComparisonFamily A)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k]
    (sq : CommSq k r p i) :
    NormalizedDerivedComparison
      (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
      (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A]
      (θ k r p i sq) :=
  constructedDerivedComparison
    (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
    (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A]
    (fun J _ => openExtension_derivedUnit_isIso A k r p i sq J)
    (θ k r p i sq)

private theorem canonical_vertical_identity
    {C D : Type v} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (G : C ⥤ C) (H : D ⥤ D) (E : C ⥤ D)
    [G.Additive] [H.Additive] [E.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (eG : G ≅ 𝟭 C) (eH : H ≅ 𝟭 D) (δ : G ⋙ E ⟶ E ⋙ H)
    (γ : G.rightDerivedFunctor ⋙ E.mapDerivedCategory ⟶
      E.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (hδ : ∀ F, δ.app F ≫ eH.hom.app (E.obj F) = E.map (eG.hom.app F))
    (hγ : ProperOpenUnitNormalized G H E E δ γ) (K : DerivedCategory C) :
    γ.app K = E.mapDerivedCategory.map
        ((G.rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryNatIso eG ≪≫
          Functor.mapDerivedCategoryIdIso C).hom.app K) ≫
      (H.rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryNatIso eH ≪≫
        Functor.mapDerivedCategoryIdIso D).inv.app (E.mapDerivedCategory.obj K) := by
  exact derived_vertical_identity G H E eG eH δ γ hδ hγ _ _
    (derived_identity_fac G eG) (derived_identity_fac H eH) K

private theorem unit_vertical_pasting
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type v}
    [Category.{w} A₀] [Category.{w} A₁] [Category.{w} A₂]
    [Category.{w} B₀] [Category.{w} B₁] [Category.{w} B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
    [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
    [Abelian.HasKInjectiveResolutions A₀] [Abelian.HasKInjectiveResolutions A₁]
    [Abelian.HasKInjectiveResolutions B₀] [Abelian.HasKInjectiveResolutions B₁]
    (G₁ : A₀ ⥤ A₁) (G₂ : A₁ ⥤ A₂) (G : A₀ ⥤ A₂)
    (H₁ : B₀ ⥤ B₁) (H₂ : B₁ ⥤ B₂) (H : B₀ ⥤ B₂)
    (E₀ : A₀ ⥤ B₀) (E₁ : A₁ ⥤ B₁) (E₂ : A₂ ⥤ B₂)
    [G₁.Additive] [G₂.Additive] [G.Additive]
    [H₁.Additive] [H₂.Additive] [H.Additive]
    [E₀.Additive] [E₁.Additive] [E₂.Additive]
    [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]
    [G₁.PreservesKInjectiveComplexes] [H₁.PreservesKInjectiveComplexes]
    (g : G₁ ⋙ G₂ ≅ G) (h : H₁ ⋙ H₂ ≅ H)
    (e₁ : G₁ ⋙ E₁ ⟶ E₀ ⋙ H₁) (e₂ : G₂ ⋙ E₂ ⟶ E₁ ⋙ H₂)
    (e : G ⋙ E₂ ⟶ E₀ ⋙ H)
    (he : ∀ X, E₂.map (g.hom.app X) ≫ e.app X =
      e₂.app (G₁.obj X) ≫ H₂.map (e₁.app X) ≫ h.hom.app (E₀.obj X))
    (c₁ : G₁.rightDerivedFunctor ⋙ E₁.mapDerivedCategory ⟶
      E₀.mapDerivedCategory ⋙ H₁.rightDerivedFunctor)
    (c₂ : G₂.rightDerivedFunctor ⋙ E₂.mapDerivedCategory ⟶
      E₁.mapDerivedCategory ⋙ H₂.rightDerivedFunctor)
    (c : G.rightDerivedFunctor ⋙ E₂.mapDerivedCategory ⟶
      E₀.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (hc₁ : ProperOpenUnitNormalized G₁ H₁ E₀ E₁ e₁ c₁)
    (hc₂ : ProperOpenUnitNormalized G₂ H₂ E₁ E₂ e₂ c₂)
    (hc : ProperOpenUnitNormalized G H E₀ E₂ e c)
    (cG : G₁.rightDerivedFunctor ⋙ G₂.rightDerivedFunctor ≅ G.rightDerivedFunctor)
    (cH : H₁.rightDerivedFunctor ⋙ H₂.rightDerivedFunctor ≅ H.rightDerivedFunctor)
    (hcG : Functor.rightDerivedFunctorCompUnit G₁ G₂ ≫
        Functor.whiskerLeft DerivedCategory.Qh cG.hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory g.hom (.up ℤ))
        DerivedCategory.Qh ≫ G.rightDerivedFunctorUnit)
    (hcH : Functor.rightDerivedFunctorCompUnit H₁ H₂ ≫
        Functor.whiskerLeft DerivedCategory.Qh cH.hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory h.hom (.up ℤ))
        DerivedCategory.Qh ≫ H.rightDerivedFunctorUnit)
    (K : DerivedCategory A₀) :
    c.app K =
      E₂.mapDerivedCategory.map
        (cG.inv.app K) ≫
      c₂.app (G₁.rightDerivedFunctor.obj K) ≫
      H₂.rightDerivedFunctor.map (c₁.app K) ≫
      cH.hom.app
        (E₀.mapDerivedCategory.obj K) := by
  exact generic_vertical_pasting G₁ G₂ G H₁ H₂ H E₀ E₁ E₂ g h e₁ e₂ e he
    c₁ c₂ c hc₁ hc₂ hc cG cH hcG hcH K

private theorem unit_horizontal_identity
    {A B : Type v} [Category.{w} A] [Category.{w} B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (G : A ⥤ B) (E : A ⥤ A) (F : B ⥤ B)
    [G.Additive] [E.Additive] [F.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (eE : E ≅ 𝟭 A) (eF : F ≅ 𝟭 B) (δ : G ⋙ F ≅ E ⋙ G)
    (γ : G.rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      E.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hδ : ∀ X, δ.hom.app X ≫ G.map (eE.hom.app X) = eF.hom.app (G.obj X))
    (hγ : ProperOpenUnitNormalized G G E F δ.hom γ.hom)
    (K : DerivedCategory A) :
    γ.hom.app K =
      (Functor.mapDerivedCategoryNatIso eF ≪≫
        Functor.mapDerivedCategoryIdIso B).hom.app (G.rightDerivedFunctor.obj K) ≫
      G.rightDerivedFunctor.map ((Functor.mapDerivedCategoryNatIso eE ≪≫
        Functor.mapDerivedCategoryIdIso A).inv.app K) := by
  exact derived_horizontal_identity G E F eE eF δ γ hδ hγ K

private theorem exists_normalized_families
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∃ (θ : ProperOpenSheafComparisonFamily A) (Γ : ProperOpenDerivedComparisonFamily A),
    (∀ {U V W Z : Scheme.{u}}
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
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F) ∧
    (∀ {U V W Z : Scheme.{u}}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
      (sq : CommSq k r p i),
      ProperOpenUnitNormalized
        (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
        (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A]
        (θ k r p i sq).hom (Γ k r p i sq).hom) := by
  generalize hθdef : @chosen_sheaf_family A _ = θ
  have hθ :
    (∀ {U V W Z : Scheme.{u}}
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
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F) := by
    intro U V W Z k r p i _ _ _ _ sq F
    rw [← hθdef]
    unfold chosen_sheaf_family
    exact (exists_sheafComparison A k r p i sq).choose_spec F
  generalize hNdef : @chosen_normalized A _ _ θ = N
  let Γ₀ : ProperOpenDerivedComparisonFamily A :=
    fun k r p i _ _ _ _ sq => (N k r p i sq).comparison
  generalize hΓdef : @Γ₀ = Γ
  have hcomp {U V W Z : Scheme.{u}}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k]
      (sq : CommSq k r p i) : (N k r p i sq).comparison = Γ k r p i sq :=
    congrArg (fun G : ProperOpenDerivedComparisonFamily A => G k r p i sq) hΓdef
  have hΓh :
    ∀ {U V W Z : Scheme.{u}}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
      (sq : CommSq k r p i),
      ProperOpenUnitNormalized
        (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
        (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A]
        (θ k r p i sq).hom (Γ k r p i sq).hom := by
    intro U V W Z k r p i _ _ _ _ sq
    rw [← hcomp k r p i sq]
    exact normalized_unit
      (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
      (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A]
      (θ k r p i sq) (N k r p i sq)
  exact ⟨@θ, @Γ, hθ, hΓh⟩

/-- Canonical proper/open interchange, with its support, representative, Cartesian,
pasting, identity and arbitrary-base-change normalizations.

Source: Stacks Project, more-etale.tex, Tags 0F7B(b), 0F7C, 0F7D, 0F7E and 0F7F;
the Cartesian mate normalization is the map in lem-sf-etale-proper-open-tensor-square.
(auxiliary; not a blueprint node).

Proof:
1. Apply lem-cbc-proper-support-sheaf-composition to identify both sheaf functors
   with the same proper-support subsheaf of (ir)_* = (pk)_*. The identification
   is the identity on sections. It is natural and satisfies ordinary vertical,
   horizontal and identity pasting, since all these words are that same identity.
2. Choose a K-injective representative with injective terms, using
   lem-pur-kinjective-degreewise-existence and the Grothendieck module-sheaf theorem.
   Locally on an affine open of Z, proper fibres have bounded dimension by
   lem-fin-finite-type-fibre-dimension-bound. The torsion proper-CD theorem and
   module/abelian comparison give finite CD for p_*. The non-Cartesian theorem
   lem-cbc-open-extended-injective-proper-acyclic gives acyclicity of every k_!I^n.
   Open restriction preserves K-injectives and injectives, since extension by zero
   is exact and left adjoint to restriction. No global quasi-compactness is needed.
3. Apply lem-kun-finite-cd-acyclic-complex locally. It says p_*rho is a quasi-isomorphism;
   the geometric stalk cohomology test glues this conclusion. For any K-injective I,
   replace it by one with injective terms. The replacement is a homotopy equivalence;
   k_! and p_* preserve homotopies, so the same conclusion holds for every I and rho.
4. Localize theta followed by p_*rho, using the exact-functor factorizations and
   lem-weil-pbc-kinjective-total-derived. The K-injective Hom bijection lifts arrows
   and comparisons of resolutions uniquely up to homotopy. Naturality of theta
   proves independence, naturality and the displayed representative normalization.
5. For a Cartesian square transpose under P_p adjoint R_p. The sheaf transpose
   is open base change followed by k_! of the ordinary r-counit: on the open it
   evaluates the same section and outside it is zero. The K-injective counit
   theorem identifies its localization with the derived counit. The mate bijection
   gives exactly openImmersionLowerShriekLowerStarExchange, with no automorphism.
6. For vertical pasting use a resolution rho:k_!I -> H. Both r1_*I and p1_*H are
   K-injective by exact inverse image and right-adjoint preservation. The first
   normalized comparison is therefore an allowed resolution for the second square.
   Composing gives p2_*p1_*rho times the ordinary pasted theta; step 1 identifies
   it with the outer theta. The K-injective direct-image compositors give the equation.
7. For horizontal pasting resolve k_!I -> H and l_!H -> L. Exactness of l_! makes
   their composite a resolution of l_!k_!I. Naturality and the ordinary horizontal
   identity of step 1 identify the two localized paths. Identity resolutions and
   the ordinary unit comparisons give the two displayed identity laws.
8. At sheaf level the two cube paths agree after inclusion in the common direct
   image: each pulls back the same section. These inclusions are monic and inverse
   image is exact. The open base-change compatibility and open-unit-mate theorem
   identify these sheaf beta maps with the inverses of the specified derived mates.
9. Choose I, rho:k_!I -> H, a K-injective resolution u:d^*I -> I1 and a resolution
   sigma:k1_!I1 -> H1. The K-injective Hom bijection gives h:a^*H -> H1 with
   h a^*rho beta_k^{-1} homotopic to sigma k1_!u. No inverse image of a K-injective
   is asserted to be K-injective. The termwise derived-exchange theorem identifies
   p1_*h times the ordinary exchange, and r1_*u times the ordinary exchange, with
   the fixed unbounded mates in the cube.
10. Insert the sheaf cube degreewise, use naturality to move rho through exchange
    and open base change, and use the homotopy in step 9. Localization makes both
    words equal. The Hom bijection gives independence of all representatives.
    Neither exchange is cancelled and the original square need not be Cartesian. -/
theorem etaleProperOpenExchangeCube
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∃ (θ : ProperOpenSheafComparisonFamily A)
      (Γ : ProperOpenDerivedComparisonFamily A),
      (∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k]
        (sq : CommSq k r p i),
        (θ k r p i sq).hom ≫
            Functor.whiskerRight
              (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k)
              (p)_*[ModuleCat.{u + 1} A] ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p (r ≫ i) sq.w.symm).hom =
          Functor.whiskerLeft (r)_*[ModuleCat.{u + 1} A]
              (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i).hom) ∧
      (∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k]
        (sq : CommSq k r p i)
        (I : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective]
        (H : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [H.IsKInjective]
        (ρ : (((k)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj I ⟶ H)
        [QuasiIso ρ],
        ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.inv.app
            ((((r)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj I) ≫
          D((i)_!open[ModuleCat.{u + 1} A]).map
            (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).inv ≫
          (Γ k r p i sq).hom.app (DerivedCategory.Q.obj I) =
        DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (θ k r p i sq).hom (.up ℤ)).app I ≫
              (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map ρ) ≫
          (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso H).inv ≫
          R((p)_*[ModuleCat.{u + 1} A]).map
            (inv (DerivedCategory.Q.map ρ) ≫
              ((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.inv.app I)) ∧
      (∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k]
        (sq : IsPullback r k i p),
        (Γ k r p i sq.toCommSq.flip).hom =
          openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq) ∧
      (∀ {U V W Z S T : Scheme.{u}}
        (k : U ⟶ V) (i₁ : W ⟶ Z) (i₂ : S ⟶ T)
        (r₁ : U ⟶ W) (p₁ : V ⟶ Z) (r₂ : W ⟶ S) (p₂ : Z ⟶ T)
        [IsProper r₁] [IsProper p₁] [IsProper r₂] [IsProper p₂]
        [IsOpenImmersion k] [IsOpenImmersion i₁] [IsOpenImmersion i₂]
        (s₁ : CommSq k r₁ p₁ i₁) (s₂ : CommSq i₁ r₂ p₂ i₂)
        (M : DerivedCategoryModule A U),
        (Γ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (s₁.vert_comp s₂)).hom.app M =
          D((i₂)_!open[ModuleCat.{u + 1} A]).map
              ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r₁ r₂).inv.app M) ≫
            (Γ i₁ r₂ p₂ i₂ s₂).hom.app (R((r₁)_*[ModuleCat.{u + 1} A]).obj M) ≫
            R((p₂)_*[ModuleCat.{u + 1} A]).map ((Γ k r₁ p₁ i₁ s₁).hom.app M) ≫
            (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p₁ p₂).hom.app
              (D((k)_!open[ModuleCat.{u + 1} A]).obj M)) ∧
      (∀ {U V V' W Z Z' : Scheme.{u}}
        (k : U ⟶ V) (l : V ⟶ V') (i : W ⟶ Z) (j : Z ⟶ Z')
        (r : U ⟶ W) (p : V ⟶ Z) (q : V' ⟶ Z')
        [IsProper r] [IsProper p] [IsProper q]
        [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
        (s₁ : CommSq k r p i) (s₂ : CommSq l p q j)
        (M : DerivedCategoryModule A U),
        (Γ (k ≫ l) r q (i ≫ j) (s₁.horiz_comp s₂)).hom.app M =
          (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) i j).hom.app
              (R((r)_*[ModuleCat.{u + 1} A]).obj M) ≫
            D((j)_!open[ModuleCat.{u + 1} A]).map ((Γ k r p i s₁).hom.app M) ≫
            (Γ l p q j s₂).hom.app (D((k)_!open[ModuleCat.{u + 1} A]).obj M) ≫
            R((q)_*[ModuleCat.{u + 1} A]).map
              ((mapDerivedCategoryOpenImmersionLowerShriekComp
                (ModuleCat.{u + 1} A) k l).inv.app M)) ∧
      (∀ {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
        (s : CommSq j (𝟙 U) (𝟙 V) j) (M : DerivedCategoryModule A U),
        (Γ j (𝟙 U) (𝟙 V) j s).hom.app M =
          D((j)_!open[ModuleCat.{u + 1} A]).map ((rightDerivedLowerStarIdIso A U).hom.app M) ≫
            (rightDerivedLowerStarIdIso A V).inv.app
              (D((j)_!open[ModuleCat.{u + 1} A]).obj M)) ∧
      (∀ {U W : Scheme.{u}} (r : U ⟶ W) [IsProper r]
        (s : CommSq (𝟙 U) r r (𝟙 W)) (M : DerivedCategoryModule A U),
        (Γ (𝟙 U) r r (𝟙 W) s).hom.app M =
          (mapDerivedCategoryOpenImmersionLowerShriekId
              (ModuleCat.{u + 1} A) W).hom.app (R((r)_*[ModuleCat.{u + 1} A]).obj M) ≫
            R((r)_*[ModuleCat.{u + 1} A]).map
              ((mapDerivedCategoryOpenImmersionLowerShriekId
                (ModuleCat.{u + 1} A) U).inv.app M)) ∧
      (∀ {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        (k₁ : U₁ ⟶ V₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁) (i₁ : W₁ ⟶ Z₁)
        (d : U₁ ⟶ U) (a : V₁ ⟶ V) (c : W₁ ⟶ W) (b : Z₁ ⟶ Z)
        [IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k]
        [IsProper p₁] [IsProper r₁] [IsOpenImmersion i₁] [IsOpenImmersion k₁]
        (s : CommSq k r p i) (s₁ : CommSq k₁ r₁ p₁ i₁)
        (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
        (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c),
        Functor.whiskerRight (Γ k r p i s).hom D((b)^*[ModuleCat.{u + 1} A]) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft D((k)_!open[ModuleCat.{u + 1} A])
            (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight
            (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
              (ModuleCat.{u + 1} A) sk).inv R((p₁)_*[ModuleCat.{u + 1} A]) ≫
          (Functor.associator _ _ _).hom =
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft R((r)_*[ModuleCat.{u + 1} A])
            (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
              (ModuleCat.{u + 1} A) si).inv ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight
            (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq)
            D((i₁)_!open[ModuleCat.{u + 1} A]) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft D((d)^*[ModuleCat.{u + 1} A]) (Γ k₁ r₁ p₁ i₁ s₁).hom) := by
  obtain ⟨θ, Γ, hθ, hΓh⟩ := exists_normalized_families A
  refine ⟨@θ, @Γ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U V W Z k r p i _ _ _ _ sq
    apply NatTrans.ext
    funext F
    have hgen (h : U ⟶ Z) (hh : h = k ≫ p) :
        (θ k r p i sq).hom.app F ≫
            ((p)_*[ModuleCat.{u + 1} A]).map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p h hh).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              (((r)_*[ModuleCat.{u + 1} A]).obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i h (hh.trans sq.w)).hom.app F := by
      subst h
      exact hθ k r p i sq F
    exact hgen (r ≫ i) sq.w.symm
  · intro U V W Z k r p i _ _ _ _ sq I _ H _ ρ _
    exact representative_inverse_formula
      (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
      (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A]
      (θ k r p i sq) (Γ k r p i sq) (hΓh k r p i sq) I H ρ
  · intro U V W Z k r p i _ _ _ _ sq
    exact etaleProperOpenCartesianNormalization A k r p i sq
      (θ k r p i sq.toCommSq.flip) (hθ k r p i sq.toCommSq.flip)
      (Γ k r p i sq.toCommSq.flip) (hΓh k r p i sq.toCommSq.flip)
  · intro U V W Z S T k i₁ i₂ r₁ p₁ r₂ p₂ _ _ _ _ _ _ _ sq₁ sq₂ K
    exact unit_vertical_pasting
      (r₁)_*[ModuleCat.{u + 1} A] (r₂)_*[ModuleCat.{u + 1} A]
      (r₁ ≫ r₂)_*[ModuleCat.{u + 1} A]
      (p₁)_*[ModuleCat.{u + 1} A] (p₂)_*[ModuleCat.{u + 1} A]
      (p₁ ≫ p₂)_*[ModuleCat.{u + 1} A]
      (k)_!open[ModuleCat.{u + 1} A] (i₁)_!open[ModuleCat.{u + 1} A]
      (i₂)_!open[ModuleCat.{u + 1} A]
      (lowerStarComp (ModuleCat.{u + 1} A) r₁ r₂)
      (lowerStarComp (ModuleCat.{u + 1} A) p₁ p₂)
      (θ k r₁ p₁ i₁ sq₁).hom (θ i₁ r₂ p₂ i₂ sq₂).hom
      (θ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂)).hom
      (ordinary_vertical A k i₁ i₂ r₁ r₂ p₁ p₂ sq₁.w sq₂.w _
        (θ k r₁ p₁ i₁ sq₁) (θ i₁ r₂ p₂ i₂ sq₂)
        (θ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂))
        (hθ k r₁ p₁ i₁ sq₁) (hθ i₁ r₂ p₂ i₂ sq₂)
        (hθ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂)))
      (Γ k r₁ p₁ i₁ sq₁).hom (Γ i₁ r₂ p₂ i₂ sq₂).hom
      (Γ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂)).hom
      (hΓh k r₁ p₁ i₁ sq₁) (hΓh i₁ r₂ p₂ i₂ sq₂)
      (hΓh k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂))
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r₁ r₂)
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p₁ p₂)
      (geometric_comp_fac A r₁ r₂) (geometric_comp_fac A p₁ p₂) K
  · intro U V V' W Z Z' k l i j r p q _ _ _ _ _ _ _ sq₁ sq₂ M
    exact etaleProperOpenHorizontalNormalization A k l r p q i j sq₁ sq₂
          (θ k r p i sq₁) (θ l p q j sq₂)
          (θ (k ≫ l) r q (i ≫ j) (sq₁.horiz_comp sq₂))
          (hθ k r p i sq₁) (hθ l p q j sq₂)
          (hθ (k ≫ l) r q (i ≫ j) (sq₁.horiz_comp sq₂))
          (Γ k r p i sq₁) (Γ l p q j sq₂)
          (Γ (k ≫ l) r q (i ≫ j) (sq₁.horiz_comp sq₂))
          (hΓh k r p i sq₁) (hΓh l p q j sq₂)
          (hΓh (k ≫ l) r q (i ≫ j) (sq₁.horiz_comp sq₂)) M
  · intro U V k _ sq K
    simp only [rightDerivedLowerStarIdIso]
    exact canonical_vertical_identity
      (lowerStar (ModuleCat.{u + 1} A) (𝟙 U))
      (lowerStar (ModuleCat.{u + 1} A) (𝟙 V))
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) k)
      (lowerStarId (ModuleCat.{u + 1} A) U)
      (lowerStarId (ModuleCat.{u + 1} A) V)
      (θ k (𝟙 U) (𝟙 V) k sq).hom
      (Γ k (𝟙 U) (𝟙 V) k sq).hom
      (ordinary_identity_vertical A k (θ k (𝟙 U) (𝟙 V) k sq)
        (hθ k (𝟙 U) (𝟙 V) k sq))
      (hΓh k (𝟙 U) (𝟙 V) k sq)
      K
  · intro U W r _ sq K
    let eU := Adjunction.leftAdjointIdIso
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 U))
      (upperStarId (ModuleCat.{u + 1} A) U)
    let eW := Adjunction.leftAdjointIdIso
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 W))
      (upperStarId (ModuleCat.{u + 1} A) W)
    simpa only [mapDerivedCategoryOpenImmersionLowerShriekId,
      openImmersionLowerShriekId, identity_leftAdjoint_compare, eU, eW]
      using unit_horizontal_identity (lowerStar (ModuleCat.{u + 1} A) r)
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 U))
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 W)) eU eW
      (θ (𝟙 U) r r (𝟙 W) sq) (Γ (𝟙 U) r r (𝟙 W) sq)
      (ordinary_identity_horizontal A r (θ (𝟙 U) r r (𝟙 W) sq)
        (hθ (𝟙 U) r r (𝟙 W) sq))
      (hΓh (𝟙 U) r r (𝟙 W) sq) K
  · intro U V W Z U₁ V₁ W₁ Z₁ k r p i k₁ r₁ p₁ i₁ d a c b
      _ _ _ _ _ _ _ _ sq sq₁ sk si sp sr
    apply NatTrans.ext
    funext M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]
    exact etaleProperOpenCubeNormalization A
      @θ @Γ
        hθ hΓh k r p i k₁ r₁ p₁ i₁ sq sq₁ a b c d sp sr si sk M

end AlgebraicGeometry.Etale
