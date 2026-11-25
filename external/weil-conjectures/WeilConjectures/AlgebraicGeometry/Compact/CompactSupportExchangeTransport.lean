/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.AlgebraicGeometry.Derived.DerivedExtensionZeroBaseChangeSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.SmoothPurity.FixSiteOpenExchange
import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareSupplement

/-!
# Transport of the chosen compact-support exchange

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-composition.proof.md, final base-change sentence, expanded by
sk-prop-sf-cbc/thm-cbc-finite-level-proetale.proof.md, lines 4--22
(blueprint: lem-pur-co-smooth-exchange-transport).

The comparisons use the normalized proper counit mate and exact open extension.
All inputs are bounded below; the pro-etale operations are ordinary ambient derived
operations. The two comparison paths are natural isomorphisms, and witness transport
retains its actual etale representative and comparison isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section ExactComparisons

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

private theorem plus_obj_obj (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : DerivedCategory.Plus C) :
    (F.mapDerivedCategoryPlus.obj K).obj = F.mapDerivedCategory.obj K.obj := rfl

private theorem inclusion_map (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map f) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := rfl

private theorem inclusion_compIso_inv (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso F G).inv.app K) =
      (Functor.mapDerivedCategoryCompIso F G).hom.app K.obj := by
  have h : DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusCompIso F G).app K) =
      (Functor.mapDerivedCategoryCompIso F G).symm.app K.obj :=
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app F G K)
  exact congrArg Iso.inv h

private theorem inclusion_natIso_inv (F G : C ⥤ D)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusNatIso e).inv.app K) =
      (Functor.mapDerivedCategoryNatIso e).inv.app K.obj := by
  have h : DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusNatIso e).app K) =
      (Functor.mapDerivedCategoryNatIso e).app K.obj :=
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app e K)
  exact congrArg Iso.inv h

private theorem inclusion_square_hom {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] (R : C ⥤ D) (G : D ⥤ B) (L : C ⥤ E) (S : E ⥤ B)
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (q : R ⋙ G ≅ L ⋙ S) (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map
        ((Functor.mapDerivedCategoryPlusSquareIso R G L S q).hom.app K) =
      (Functor.mapDerivedCategorySquareIso q).hom.app K.obj := by
  simp only [Functor.mapDerivedCategoryPlusSquareIso, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    inclusion_compIso_inv, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  rfl

private theorem plusNatIso_symm (F G : C ⥤ D)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryPlusNatIso e.symm =
      (Functor.mapDerivedCategoryPlusNatIso e).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Iso.symm_hom]
  rw [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app, inclusion_natIso_inv]
  exact congrArg (fun t ↦ t.app K.obj) (Functor.mapDerivedCategoryNatIso_symm e)

private theorem plusSquare_symm {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] (R : C ⥤ D) (G : D ⥤ B) (L : C ⥤ E) (S : E ⥤ B)
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (q : R ⋙ G ≅ L ⋙ S) :
    Functor.mapDerivedCategoryPlusSquareIso L S R G q.symm =
      (Functor.mapDerivedCategoryPlusSquareIso R G L S q).symm := by
  simp only [Functor.mapDerivedCategoryPlusSquareIso, plusNatIso_symm]
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc]

private theorem plus_square_eq {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] (R : C ⥤ D) (G : D ⥤ B) (L : C ⥤ E) (S : E ⥤ B)
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (q : R ⋙ G ≅ L ⋙ S)
    (e : R.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ≅
      L.mapDerivedCategoryPlus ⋙ S.mapDerivedCategoryPlus)
    (h : ∀ K : HomotopyCategory.Plus C,
      e.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        S.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        S.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
      G.mapDerivedCategoryPlus.map (R.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        G.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus q.hom).app K)) :
    e.hom = (Functor.mapDerivedCategoryPlusSquareIso R G L S q).hom := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)
  intro K
  apply (cancel_mono (S.mapDerivedCategoryPlus.map
      (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    S.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K))).mp
  rw [h, Functor.mapDerivedCategoryPlusSquareIso_fac]

private theorem inclusion_unit_generic (F : C ⥤ D) (G : D ⥤ C)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F.mapDerivedCategory ⊣ G.mapDerivedCategory) (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map
      ((adj.restrictFullyFaithful (ObjectProperty.fullyFaithfulι _)
        (ObjectProperty.fullyFaithfulι _) F.mapDerivedCategoryPlusCompatibility.symm
        G.mapDerivedCategoryPlusCompatibility.symm).unit.app K) =
      adj.unit.app K.obj := by
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app]
  change adj.unit.app K.obj ≫ G.mapDerivedCategory.map (𝟙 _) ≫ 𝟙 _ = _
  simp only [CategoryTheory.Functor.map_id, Functor.comp_obj, Category.comp_id]

private theorem plus_unit_square {C₁ D₁ C₂ D₂ : Type*}
    [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
    [HasDerivedCategory C₁] [HasDerivedCategory D₁]
    [HasDerivedCategory C₂] [HasDerivedCategory D₂]
    (f₁ : C₁ ⥤ D₁) (g₁ : D₁ ⥤ C₁) (f₂ : C₂ ⥤ D₂) (g₂ : D₂ ⥤ C₂)
    (a : C₁ ⥤ C₂) (b : D₁ ⥤ D₂)
    [f₁.Additive] [g₁.Additive] [f₂.Additive] [g₂.Additive] [a.Additive] [b.Additive]
    [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
    [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
    [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
    [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
    [PreservesFiniteLimits a] [PreservesFiniteColimits a]
    [PreservesFiniteLimits b] [PreservesFiniteColimits b]
    (adj₁ : f₁.mapDerivedCategory ⊣ g₁.mapDerivedCategory)
    (adj₂ : f₂.mapDerivedCategory ⊣ g₂.mapDerivedCategory)
    (τ : g₁ ⋙ a ≅ b ⋙ g₂) (β : a ⋙ f₂ ≅ f₁ ⋙ b)
    (h : ∀ K : _root_.DerivedCategory C₁,
      adj₂.unit.app (a.mapDerivedCategory.obj K) ≫
        g₂.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso β).hom.app K) =
      a.mapDerivedCategory.map (adj₁.unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso τ).hom.app (f₁.mapDerivedCategory.obj K))
    (K : DerivedCategory.Plus C₁) :
    (adj₂.restrictFullyFaithful (ObjectProperty.fullyFaithfulι _)
        (ObjectProperty.fullyFaithfulι _) f₂.mapDerivedCategoryPlusCompatibility.symm
        g₂.mapDerivedCategoryPlusCompatibility.symm).unit.app
          (a.mapDerivedCategoryPlus.obj K) ≫
      g₂.mapDerivedCategoryPlus.map
        ((Functor.mapDerivedCategoryPlusSquareIso _ _ _ _ β).hom.app K) =
    a.mapDerivedCategoryPlus.map
        ((adj₁.restrictFullyFaithful (ObjectProperty.fullyFaithfulι _)
          (ObjectProperty.fullyFaithfulι _) f₁.mapDerivedCategoryPlusCompatibility.symm
          g₁.mapDerivedCategoryPlusCompatibility.symm).unit.app K) ≫
      (Functor.mapDerivedCategoryPlusSquareIso _ _ _ _ τ).hom.app
        (f₁.mapDerivedCategoryPlus.obj K) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, inclusion_map, inclusion_unit_generic,
    inclusion_square_hom, plus_obj_obj]
  exact h K.obj

end ExactComparisons

private theorem inverse_mate_eq {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (γ : R₁ ⋙ G ⟶ H ⋙ R₂)
    (h : ∀ a, G.map (adj₁.unit.app a) ≫ γ.app (L₁.obj a) =
      adj₂.unit.app (G.obj a) ≫ R₂.map (α.app a)) :
    ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ γ)) = α := by
  have hm := mateEquiv_eq_of_unit adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)
    (TwoSquare.mk _ _ _ _ γ) h
  rw [← hm]
  exact (Equiv.symm_apply_apply _ _)

private theorem formalism_exchange_app (F : AlgebraicGeometry.CompactSupportFormalism)
    [F.HasProperExchange]
    {X' X Y' Y : AlgebraicGeometry.Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : AlgebraicGeometry.Compactification f)
    (K : F.obj X) :
    letI := AlgebraicGeometry.CompactSupportFormalism.HasBaseChange.isIso_baseChange
      (F := F) (c.isPullback_i_ofIsPullback sq)
    (F.shriekBaseChangeOfIsPullback sq c).app K =
      (F.pfBaseChange (pullback.fst c.g g) (c.ofIsPullback sq).g c.g g
        (c.isPullback_g_ofIsPullback sq).flip.w).app ((F.sh c.i).obj K) ≫
      (F.pf (c.ofIsPullback sq).g).map
        ((inv (F.baseChange g' (c.ofIsPullback sq).i c.i (pullback.fst c.g g)
          (c.isPullback_i_ofIsPullback sq).w)).app K) := by
  simp only [AlgebraicGeometry.CompactSupportFormalism.shriekBaseChangeOfIsPullback,
    AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange,
    CategoryTheory.ExchangeFormalism.shriekBaseChange,
    TwoSquare.hComp, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  exact Category.id_comp _

private theorem formalism_exchange_app_eq (F : AlgebraicGeometry.CompactSupportFormalism)
    [F.HasProperExchange] {X' X Y' Y : AlgebraicGeometry.Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : AlgebraicGeometry.Compactification f)
    (p : F.pf c.g ⋙ F.pb g ⟶ F.pb (pullback.fst c.g g) ⋙ F.pf (c.ofIsPullback sq).g)
    (β : F.sh c.i ⋙ F.pb (pullback.fst c.g g) ⟶ F.pb g' ⋙ F.sh (c.ofIsPullback sq).i)
    (hp : (F.pfBaseChange (pullback.fst c.g g) (c.ofIsPullback sq).g c.g g
      (c.isPullback_g_ofIsPullback sq).flip.w) = p)
    (ho :
      letI := AlgebraicGeometry.CompactSupportFormalism.HasBaseChange.isIso_baseChange
        (F := F) (c.isPullback_i_ofIsPullback sq)
      inv (F.baseChange g' (c.ofIsPullback sq).i c.i (pullback.fst c.g g)
        (c.isPullback_i_ofIsPullback sq).w) = β)
    (K : F.obj X) :
    (F.shriekBaseChangeOfIsPullback sq c).app K =
      p.app ((F.sh c.i).obj K) ≫ (F.pf (c.ofIsPullback sq).g).map (β.app K) := by
  rw [formalism_exchange_app, hp, ho]

private theorem etale_formalism_exchange_app (A : Type*) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [(AlgebraicGeometry.Etale.derivedPlusFormalism A).HasProperExchange]
    {X' X Y' Y : AlgebraicGeometry.Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : AlgebraicGeometry.Compactification f)
    (β : (AlgebraicGeometry.Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus ⋙
        (AlgebraicGeometry.Etale.upperStar A (pullback.fst c.g g)).mapDerivedCategoryPlus ⟶
      (AlgebraicGeometry.Etale.upperStar A g').mapDerivedCategoryPlus ⋙
        (AlgebraicGeometry.Etale.openImmersionLowerShriek
          A (c.ofIsPullback sq).i).mapDerivedCategoryPlus)
    (ho :
      letI := AlgebraicGeometry.CompactSupportFormalism.HasBaseChange.isIso_baseChange
        (F := AlgebraicGeometry.Etale.derivedPlusFormalism A) (c.isPullback_i_ofIsPullback sq)
      inv ((AlgebraicGeometry.Etale.derivedPlusFormalism A).baseChange g'
        (c.ofIsPullback sq).i c.i (pullback.fst c.g g)
        (c.isPullback_i_ofIsPullback sq).w) = β)
    :
    ((AlgebraicGeometry.Etale.derivedPlusFormalism A).shriekBaseChangeOfIsPullback
      sq c) =
      Functor.whiskerLeft
        (AlgebraicGeometry.Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus
        (AlgebraicGeometry.Etale.baseChange A
          (c.isPullback_g_ofIsPullback sq).flip.toCommSq) ≫
      Functor.whiskerRight β
        (AlgebraicGeometry.Etale.lowerStar A (c.ofIsPullback sq).g).rightDerivedFunctorPlus := by
  apply NatTrans.ext
  funext K
  have hp := (AlgebraicGeometry.Etale.baseChange_eq_derivedBaseChangeMapPlus
    A (c.isPullback_g_ofIsPullback sq).flip.toCommSq).symm
  exact formalism_exchange_app_eq (AlgebraicGeometry.Etale.derivedPlusFormalism A)
    sq c (AlgebraicGeometry.Etale.baseChange A
      (c.isPullback_g_ofIsPullback sq).flip.toCommSq) β
    ((AlgebraicGeometry.Etale.derivedPlusFormalism_pfBaseChange A
      _ _ _ _ (c.isPullback_g_ofIsPullback sq).flip.w).trans hp) ho K

namespace AlgebraicGeometry.ProEtale

/-- The normalized proper/open comparison, with bounded-below etale source and ambient
pro-etale target. This only inserts the canonical bounded-below inclusions into the
existing compact-support site comparison; its proper factor is the counit mate.
Source: blueprint finite-level compact-support transport proof, lines 4--19
(blueprint: lem-pur-co-smooth-exchange-transport). -/
def compactExchangeTransportComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ⋙
        DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory ⋙
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} Λ) c) _ ≪≫
    Functor.associator _ _ _ ≪≫
    (compactSupportSiteComparison Λ c).symm

private theorem compactComparison_hom (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactExchangeTransportComparison Λ c).hom.app K =
      (rightDerivedLowerStarComparisonIso' c.g (ModuleCat.{u + 1} Λ)).hom.app
        ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj K) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctor.map
        ((fixSiteOpenComparison Λ c.i).hom.app K.obj) := by
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, compactExchangeTransportComparison, compactSupportSiteComparison,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [compactSupportSiteComparisonPlus,
    rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    rightDerivedLowerStarComparisonIso', rightDerivedLowerStarComparisonPlusIso,
    Functor.mapDerivedCategoryPlusCompatibility,
    Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj]
  simp only [plus_obj_obj, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  have hn :=
    (lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctorPlusCompatibility.hom.naturality
      ((properOpenSiteExtensionIso Λ c.i).hom.app K)
  change DerivedCategory.Plus.ι.map
      ((lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctorPlus.map
        ((properOpenSiteExtensionIso Λ c.i).hom.app K)) ≫ _ = _ at hn
  have he : DerivedCategory.Plus.ι.map
      ((properOpenSiteExtensionIso Λ c.i).hom.app K) =
      (fixSiteOpenComparison Λ c.i).hom.app K.obj := by
    exact inclusion_square_hom
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) c.Z)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i)
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) c.i) K
  change _ ≫ _ = _ ≫ _ at hn
  simp only [Functor.comp_map] at hn
  simpa only [Functor.mapDerivedCategoryPlusCompatibility,
    fixedComparisonDirectImageMatePlus, asIso_hom, Functor.comp_obj,
    rightDerivedLowerStarComparisonPlusBaseChange,
    ObjectProperty.ι_obj, Category.assoc, he,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] using
    congrArg (fun t ↦ DerivedCategory.Plus.ι.map
      ((fixedComparisonDirectImageMatePlus Λ c.g).app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj
          K)) ≫ t) hn

/-- The source path `S = v^* C_c ∘ a_v` as a natural isomorphism.
Source: blueprint finite-level compact-support transport proof, lines 4--20
(blueprint: lem-pur-co-smooth-exchange-transport). -/
def compactExchangeTransportSource (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f) :
    (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ⋙
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus) ⋙
          DerivedCategory.Plus.ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory ≅
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory ⋙
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) ⋙
            (upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarComparisonIso g Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (compactExchangeTransportComparison Λ c) _

/-- The target path `T = F_{u'}^p(a_w) ∘ C_{c'}` as a natural isomorphism.
Source: blueprint finite-level compact-support transport proof, lines 15--20
(blueprint: lem-pur-co-smooth-exchange-transport). -/
def compactExchangeTransportTarget (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (c : Compactification f) :
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus ⋙
        Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
          (c.ofIsPullback sq)) ⋙ DerivedCategory.Plus.ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory ≅
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory ⋙
          (upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor) ⋙
            rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
              (c.ofIsPullback sq) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (compactExchangeTransportComparison Λ (c.ofIsPullback sq)) ≪≫
    (Functor.associator
      (Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory)
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (c.ofIsPullback sq))).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarComparisonIso g' Λ) _

/-- Transport the specified etale exchange through a retained etale-origin witness
`(L, alpha)` in the fixed-scalar module-sheaf presentation. Both endpoint paths are
canonical, so this definition contains no arbitrary exchange or comparison choice.
Source: blueprint finite-level compact-support transport proof, lines 21--22
(blueprint: lem-pur-co-smooth-exchange-transport). -/
def compactExchangeTransportAtWitness (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (alpha : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L.obj ≅ N) :
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) ⋙
        (upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor).obj N ⟶
      ((upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
          (c.ofIsPullback sq)).obj N :=
  ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) ⋙
      (upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor).map alpha.inv ≫
    (compactExchangeTransportSource Λ g c).inv.app L ≫
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c).app L)) ≫
    (compactExchangeTransportTarget Λ sq c).hom.app L ≫
    ((upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (c.ofIsPullback sq)).map alpha.hom

private theorem pullbackSquare_hom (A : Type*) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    (Etale.pullbackSquareComparison A sq).hom =
      (Functor.mapDerivedCategoryPlusSquareIso _ _ _ _
        (Etale.squareUpperStarIso A sq)).hom := by
  with_unfolding_all
    exact plus_square_eq
      (Etale.upperStar A g)
      (Etale.upperStar A f')
      (Etale.upperStar A f)
      (Etale.upperStar A g')
      (Etale.squareUpperStarIso A sq)
      (Etale.pullbackSquareComparison A sq)
      (Etale.pullbackSquareComparison_hom_app_factorsh A sq)

-- Comparing the two expanded square isomorphisms requires additional elaboration steps.
private theorem formalism_square_hom (Λ : Type (u + 1)) [CommRing Λ]
    {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} (sq : CommSq t l r b) :
    ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).sqIso t l r b sq.w).hom =
      (Functor.mapDerivedCategoryPlusSquareIso _ _ _ _
        (Etale.squareUpperStarIso (ModuleCat.{u + 1} Λ) sq.flip)).hom := by
  with_unfolding_all
    rw [Etale.derivedPlusFormalism_sqIso]
    have h := pullbackSquare_hom (ModuleCat.{u + 1} Λ) sq
    have he : Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq =
        Functor.mapDerivedCategoryPlusSquareIso _ _ _ _
          (Etale.squareUpperStarIso (ModuleCat.{u + 1} Λ) sq) := Iso.ext h
    rw [he, Etale.squareUpperStarIso_flip (ModuleCat.{u + 1} Λ) sq.flip,
      plusSquare_symm]
    rfl

private theorem formalism_open_hom (Λ : Type (u + 1)) [CommRing Λ]
    {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).baseChange t l r b sq.w) =
      (Functor.mapDerivedCategoryPlusSquareIso _ _ _ _
        (@asIso _ _ _ _ _ (Etale.isIso_openImmersionLowerShriekBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq))).hom := by
  with_unfolding_all
    rw [ExchangeFormalism.baseChange, formalism_square_hom Λ sq.toCommSq]
    let A := ModuleCat.{u + 1} Λ
    let β := @asIso _ _ _ _ _ (Etale.isIso_openImmersionLowerShriekBaseChangeMap A sq)
    change ((mateEquiv
      (Etale.openImmersionLowerShriekUpperStarAdjunction A r).mapDerivedCategoryPlusAdjunction
      (Etale.openImmersionLowerShriekUpperStarAdjunction A l).mapDerivedCategoryPlusAdjunction).symm
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategoryPlusSquareIso _ _ _ _
          (Etale.squareUpperStarIso A sq.toCommSq.flip)).hom)) = _
    apply inverse_mate_eq
    intro K
    symm
    exact plus_unit_square _ _ _ _ _ _
      (Etale.openImmersionLowerShriekUpperStarAdjunction A r).mapDerivedCategoryAdjunction
      (Etale.openImmersionLowerShriekUpperStarAdjunction A l).mapDerivedCategoryAdjunction
      (Etale.squareUpperStarIso A sq.toCommSq.flip) β
      (Adjunction.mapDerivedCategoryAdjunction_mate
        (Etale.openImmersionLowerShriekUpperStarAdjunction A r)
        (Etale.openImmersionLowerShriekUpperStarAdjunction A l)
        (Etale.squareUpperStarIso A sq.toCommSq.flip) β
        (fun M ↦ Etale.unit_map_openImmersionLowerShriekBaseChangeMap_app A sq.toCommSq M)) K

private theorem formalism_open_inv (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    let := Etale.isIso_derivedPlusFormalism_baseChange Λ sq
    inv (((Etale.derivedPlusFormalism (ModuleCat.{u + 1} Λ)).baseChange t l r b sq.w)) =
      (Etale.extensionZeroBaseChangeDerivedPlusIso Λ sq).hom := by
  with_unfolding_all
    let := Etale.isIso_derivedPlusFormalism_baseChange Λ sq
    apply IsIso.inv_eq_of_hom_inv_id
    rw [formalism_open_hom Λ sq]
    let β := @asIso _ _ _ _ _ (Etale.isIso_openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} Λ) sq)
    change (Functor.mapDerivedCategoryPlusSquareIso _ _ _ _ β).hom ≫
      (Functor.mapDerivedCategoryPlusSquareIso _ _ _ _ β.symm).hom = _
    rw [plusSquare_symm]
    exact Iso.hom_inv_id _

private theorem ordinary_open_hom (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    (ordinaryOpenExtensionBaseChangeIso Λ t l r b sq).hom =
      (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sq).inv := by
  let A := ModuleCat.{u + 1} Λ
  have he :
      (conjugateIsoEquiv
        ((openImmersionLowerShriekUpperStarAdjunction A r).comp
          (upperStarLowerStarAdjunction A b))
        ((upperStarLowerStarAdjunction A t).comp
          (openImmersionLowerShriekUpperStarAdjunction A l))).symm
          (@asIso _ _ _ _ (baseChangeMap A sq.toCommSq)
            (isIso_baseChangeMap_of_isPullback A sq)) =
        @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A sq) := by
    apply Iso.ext
    rfl
  simp only [ordinaryOpenExtensionBaseChangeIso,
    derivedOpenImmersionLowerShriekBaseChangeIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm,
    openImmersionLowerShriekBaseChangeIso, Category.assoc]
  rw [he]

private theorem pullbackComparison_hom (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (g : U ⟶ X)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComparisonIso g Λ).hom.app K =
      (fixSitePullbackComparison Λ g).inv.app K.obj ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj K.obj) := by
  simp [leftDerivedUpperStarComparisonIso, fixSitePullbackComparison,
    Functor.mapDerivedCategoryNatIso_symm, Functor.mapDerivedCategoryPlusCompatibility,
    Category.assoc]

private theorem open_transport (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b)
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComparisonIso b Λ).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) r).mapDerivedCategoryPlus.obj K) ≫
      (upperStar (ModuleCat.{u + 1} Λ) b).leftDerivedFunctor.map
        ((fixSiteOpenComparison Λ r).hom.app K.obj) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) b).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) r).mapDerivedCategory.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj K.obj)) ≫
      (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sq).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj K.obj) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) l).mapDerivedCategory.map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) t).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj K.obj)) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Z').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((Etale.extensionZeroBaseChangeDerivedPlusIso Λ sq).hom.app K)) ≫
      (fixSiteOpenComparison Λ l).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) t).mapDerivedCategory.obj K.obj) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) l).mapDerivedCategory.map
        ((leftDerivedUpperStarComparisonIso t Λ).hom.app K) := by
  let A := ModuleCat.{u + 1} Λ
  let osq : OpenImmersionSquare t l r b :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd
      isOpenImmersion := inferInstance
      isOpenImmersion' := inferInstance }
  have ho := fixSiteOpenExchange Λ osq K
  have ho' := congrArg (fun z ↦ (fixSitePullbackComparison Λ b).inv.app
      ((Etale.openImmersionLowerShriek A r).mapDerivedCategory.obj K.obj) ≫ z ≫
      (openImmersionLowerShriek A l).mapDerivedCategory.map
        ((fixSitePullbackComparison Λ t).inv.app K.obj)) ho
  dsimp only [A, Functor.comp_obj, ObjectProperty.ι_obj] at ho'
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app_assoc] at ho'
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at ho'
  simp only [pullbackComparison_hom, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj]
  erw [← reassoc_of%
    ((leftDerivedUpperStarIsoMapDerivedCategory A b).inv.naturality
      ((fixSiteOpenComparison Λ r).hom.app K.obj))]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← ordinary_open_hom Λ sq]
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    Functor.comp_obj, ObjectProperty.ι_obj]
  with_unfolding_all
    simpa only [Category.assoc, Functor.map_comp] using congrArg
      (fun z ↦ z ≫ (openImmersionLowerShriek A l).mapDerivedCategory.map
        ((leftDerivedUpperStarIsoMapDerivedCategory A t).inv.app
          ((comparisonUpperStar A U).mapDerivedCategory.obj K.obj))) ho'

private theorem etale_exchange_eq (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (c : Compactification f)
    :
    Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c =
      Functor.whiskerLeft
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus
        (Etale.baseChange (ModuleCat.{u + 1} Λ)
          (c.isPullback_g_ofIsPullback sq).flip.toCommSq) ≫
      Functor.whiskerRight
        (Etale.extensionZeroBaseChangeDerivedPlusIso Λ (c.isPullback_i_ofIsPullback sq)).hom
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq).g).rightDerivedFunctorPlus := by
  exact etale_formalism_exchange_app (ModuleCat.{u + 1} Λ) sq c
    (Etale.extensionZeroBaseChangeDerivedPlusIso Λ (c.isPullback_i_ofIsPullback sq)).hom
    (formalism_open_inv Λ (c.isPullback_i_ofIsPullback sq))

private theorem etale_exchange_app (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c).app K =
      (Etale.baseChange (ModuleCat.{u + 1} Λ)
        (c.isPullback_g_ofIsPullback sq).flip.toCommSq).app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj
            K) ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq).g).rightDerivedFunctorPlus.map
            ((Etale.extensionZeroBaseChangeDerivedPlusIso Λ
              (c.isPullback_i_ofIsPullback sq)).hom.app K) := by
  exact NatTrans.congr_app (etale_exchange_eq Λ sq c) K

private theorem proetale_exchange_app (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} Λ) sq c).app K =
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
        (c.isPullback_g_ofIsPullback sq).flip.toCommSq).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategory.obj K) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq).g).rightDerivedFunctor.map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ)
            (pullback.fst c.g g)).hom.app
              ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategory.obj K) ≫
            (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ)
              (c.isPullback_i_ofIsPullback sq)).inv.app K ≫
            (openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
              (c.ofIsPullback sq).i).mapDerivedCategory.map
                ((leftDerivedUpperStarIsoMapDerivedCategory
                  (ModuleCat.{u + 1} Λ) g').inv.app K)) := by
  simp [rightDerivedLowerShriekOfCompactificationBaseChangeMap,
    rightDerivedLowerShriekOfCompactificationBaseChangeIso]

/-- The canonical compact-support exchange square.
Source: blueprint finite-level compact-support transport proof, lines 4--20
(blueprint: lem-pur-co-smooth-exchange-transport). -/
private theorem compactSupport_exchange_transport_square
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    (Functor.whiskerRight
        (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c)
        (DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory) ≫
      (compactExchangeTransportTarget Λ sq c).hom =
    (compactExchangeTransportSource Λ g c).hom ≫
      Functor.whiskerLeft
        (DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory)
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq c)) := by
  with_unfolding_all
    apply NatTrans.ext
    funext K
    let A := ModuleCat.{u + 1} Λ
    let M := (Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus.obj K
    let P' := (lowerStar A (c.ofIsPullback sq).g).rightDerivedFunctor
    let e := (fixSiteOpenComparison Λ c.i).hom.app K.obj
    let β := (Etale.extensionZeroBaseChangeDerivedPlusIso Λ
      (c.isPullback_i_ofIsPullback sq)).hom.app K
    have hp := comparison_derivedBaseChangeMap Λ
      (c.isPullback_g_ofIsPullback sq).flip M
    have ho := open_transport Λ (c.isPullback_i_ofIsPullback sq) K
    have hn := (derivedBaseChangeMap A
      (c.isPullback_g_ofIsPullback sq).flip.toCommSq).naturality e
    have hb := (rightDerivedLowerStarComparisonIso' (c.ofIsPullback sq).g A).hom.naturality β
    simp only [baseChangeSourceComparisonIso, baseChangeTargetComparisonIso,
      Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hp
    simp only [Functor.comp_map] at hn hb
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      compactExchangeTransportTarget, compactExchangeTransportSource,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, compactComparison_hom,
      etale_exchange_app, proetale_exchange_app, Functor.comp_map, Functor.map_comp, Category.assoc]
    dsimp only [A, β, P', Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
      Functor.comp_obj, ObjectProperty.ι_obj] at *
    simp only [Category.id_comp] at *
    -- Move the proper comparison across the etale open exchange.
    rw [reassoc_of% hb]
    -- Combine the three images of the open square, and use its compatibility.
    simp only [← Functor.map_comp]
    rw [← ho]
    simp only [Functor.map_comp]
    simp only [Category.assoc] at hp hn
    -- The remaining square is proper base change, followed by its naturality in e.
    erw [reassoc_of% hp]
    erw [← reassoc_of% hn]
    rfl

/-- The normalized compact-support comparison identifies the specified etale and
ambient pro-etale exchanges, naturally in every bounded-below input. Transport through
any retained witness equals the ambient exchange at its target; hence it is unchanged
under isomorphisms of witnesses (indeed it is independent of the witness).
Source: blueprint main-20261015, lem-pur-co-smooth-composition.proof.md, final sentence;
thm-cbc-finite-level-proetale.proof.md, lines 4--22
(blueprint: lem-pur-co-smooth-exchange-transport).

Proof plan, following the node's four steps:
1. Put M = j_! L. Exact open extension preserves bounded-below objects. The proper
parts of c and its base change are qcqs. Apply lemma-naturality-pasting-comparison--3
at M, using the normalized mate of lem-weil-pbc-comparison-direct-image-canonical-mate.
This gives the proper exchange square, without assuming its invertibility or any
separatedness of g.
2. The degreewise site/open comparisons are those of
proposition-comparison-immersions--1. Apply lem-fix-site-open-exchange to the upper
open square, with rho = a^{-1}, and multiply by the two pullback comparisons. This says
beta^p A(L) composed with the pulled-back site/open comparison and a_bar equals
j'_!(a_w) composed with the base-changed site/open comparison and A(beta^e).
3. Expand both compact-support exchanges as the proper exchange followed by the image
of beta. Naturality of the pro-etale proper exchange moves the open comparison across
it. Substitute the proper square from step 1 and the open square from step 2. Naturality
of the base-changed proper mate then gives T A(E^e) = E^p S. All factors are natural;
thus the equation is an equality of natural transformations.
4. Conjugate the equation by S^{-1} and by the source and target images of alpha.
Naturality of E^p in alpha cancels these images, leaving precisely E^p(N). This right
side contains no witness, proving the stated invariance, including isomorphic witnesses.
The identity base change, identity open/proper factors, empty schemes and zero ring
are included. No completion is used. -/
theorem compactSupport_exchange_transport
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    (Functor.whiskerRight
        (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c)
        (DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory) ≫
      (compactExchangeTransportTarget Λ sq c).hom =
    (compactExchangeTransportSource Λ g c).hom ≫
      Functor.whiskerLeft
        (DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory)
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq c)) ∧
    (∀ (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
      (alpha : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L.obj ≅ N),
      compactExchangeTransportAtWitness Λ sq c L N alpha =
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq c).app N) := by
  have h := compactSupport_exchange_transport_square Λ sq c
  refine ⟨h, ?_⟩
  intro L N alpha
  have hL := congrArg (fun t ↦ t.app L) h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_map] at hL
  dsimp only [compactExchangeTransportAtWitness]
  rw [reassoc_of% hL]
  simp only [Iso.inv_hom_id_app_assoc]
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ⋙
    (upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor
  let G := (upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor ⋙
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq)
  let E : F ⟶ G := rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} Λ) sq c
  change F.map alpha.inv ≫ E.app _ ≫ G.map alpha.hom = E.app N
  rw [← E.naturality, ← F.map_comp_assoc, alpha.inv_hom_id, F.map_id,
    Category.id_comp]

end AlgebraicGeometry.ProEtale
