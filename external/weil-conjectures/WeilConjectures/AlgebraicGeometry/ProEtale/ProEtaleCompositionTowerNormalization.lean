/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerDefinitions
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientMate
import all WeilConjectures.AlgebraicGeometry.Open.OpenSiteEvaluationCounit
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedExchangeAgrees
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportProperFactor
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerDefinitions

set_option linter.privateModule false

/-!
# Normalization on a compatible pro-etale compactification tower

The two sides below are independently constructed: the canonical origin compositor,
conjugated to the supplied candidates by canonical comparisons, and the open adjunct of
inverse ordinary exchange followed by the direct-image and open-extension compositors.

## References

* Stacks Tags 0F7B and 0F7J
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option maxErrors 1
set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

attribute [local implicit_reducible] Functor.mapDerivedCategoryPlus
  Etale.rightDerivedLowerStarPlus

private instance tower_plus_open_unit_isIso {H T : Scheme.{u}}
    (b : H ⟶ T) [IsOpenImmersion b] :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) b).unit := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus (ModuleCat.{u + 1} Λ) b
  have ff := a.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (asIso (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) b).unit).symm ≪≫
      Functor.mapDerivedCategoryPlusIdIso _)
  have := ff.full
  have := ff.faithful
  exact a.unit_isIso_of_L_fully_faithful

private abbrev towerPlusExchange {H T V S : Scheme.{u}}
    (b : H ⟶ T) (i : V ⟶ S) (r : H ⟶ V) (p : T ⟶ S)
    (w : b ≫ p = r ≫ i) :=
  (mateEquiv
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) p)
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) r)
    ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (upperStarCompIso (ModuleCat.{u + 1} Λ) w.symm) ≪≫
      Functor.mapDerivedCategoryPlusCompIso _ _).hom)

private def towerPlusLambda {H T V S : Scheme.{u}}
    (b : H ⟶ T) (i : V ⟶ S) (r : H ⟶ V) (p : T ⟶ S)
    [IsOpenImmersion b] (w : b ≫ p = r ≫ i)
    (N : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology H) (ModuleCat.{u + 1} Λ))) :=
  (towerPlusExchange Λ b i r p w).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.obj N) ≫
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.map
      (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) b).unit.app N))

section
variable {E₀ E₁ E₂ E₃ P₀ P₁ P₂ P₃ : Type*}
  [Category E₀] [Category E₁] [Category E₂] [Category E₃]
  [Category P₀] [Category P₁] [Category P₂] [Category P₃]
  {l : E₀ ⥤ E₁} {r : E₁ ⥤ E₀} {l' : E₂ ⥤ E₃} {r' : E₃ ⥤ E₂}
  {p : P₀ ⥤ P₁} {s : P₁ ⥤ P₀} {p' : P₂ ⥤ P₃} {s' : P₃ ⥤ P₂}
  (e : l ⊣ r) (e' : l' ⊣ r') (d : p ⊣ s) (d' : p' ⊣ s')
  {g : E₀ ⥤ E₂} {h : E₁ ⥤ E₃} {q : P₀ ⥤ P₂} {t : P₁ ⥤ P₃}
  {A₀ : E₀ ⥤ P₀} {A₁ : E₁ ⥤ P₁} {A₂ : E₂ ⥤ P₂} {A₃ : E₃ ⥤ P₃}
  (a : l ⋙ A₁ ≅ A₀ ⋙ p) (a' : l' ⋙ A₃ ≅ A₂ ⋙ p')
  (c : g ⋙ A₂ ≅ A₀ ⋙ q) (c' : h ⋙ A₃ ≅ A₁ ⋙ t)
  (b : r ⋙ A₀ ⟶ A₁ ⋙ s) (b' : r' ⋙ A₂ ⟶ A₃ ⋙ s')
  (θ : g ⋙ l' ⟶ l ⋙ h) (ϑ : q ⋙ p' ⟶ p ⋙ t)
  (hb : ∀ K, a.hom.app (r.obj K) ≫ p.map (b.app K) ≫ d.counit.app (A₁.obj K) =
    A₁.map (e.counit.app K))
  (hb' : ∀ K, a'.hom.app (r'.obj K) ≫ p'.map (b'.app K) ≫ d'.counit.app (A₃.obj K) =
    A₃.map (e'.counit.app K))
  (hsq : ∀ M, A₃.map (θ.app M) ≫ c'.hom.app (l.obj M) ≫ t.map (a.hom.app M) =
    a'.hom.app (g.obj M) ≫ p'.map (c.hom.app M) ≫ ϑ.app (A₀.obj M))

include a a' hb hb' hsq in
private theorem towerSiteMate_transport (K : E₁) :
    A₂.map ((mateEquiv e e' (TwoSquare.mk _ _ _ _ θ)).app K) ≫ b'.app (h.obj K) ≫
      s'.map (c'.hom.app K) =
    c.hom.app (r.obj K) ≫ q.map (b.app K) ≫
      (mateEquiv d d' (TwoSquare.mk _ _ _ _ ϑ)).app (A₁.obj K) := by
  apply (d'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  apply (cancel_epi (a'.hom.app (g.obj (r.obj K)))).1
  have hn := a'.hom.naturality ((mateEquiv e e' (TwoSquare.mk _ _ _ _ θ)).app K)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [d'.counit_naturality, reassoc_of% hb']
  rw [← A₃.map_comp_assoc, mateEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hn' := c'.hom.naturality (e.counit.app K)
  simp only [Functor.comp_map] at hn'
  erw [hn', mateEquiv_counit]
  have ht := ϑ.naturality (b.app K)
  simp only [Functor.comp_map] at ht
  erw [reassoc_of% ht, ← reassoc_of% hsq]
  simp only [← Functor.map_comp, hb, TwoSquare.mk, Functor.comp_obj]

end

private theorem tower_exchange_plus {H T V S : Scheme.{u}}
    (b : H ⟶ T) (i : V ⟶ S) (r : H ⟶ V) (p : T ⟶ S)
    (w : b ≫ p = r ≫ i)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.Plus.ι.map ((towerPlusExchange Λ b i r p w).app K) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusCompatibility.hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.obj K) =
      (towerPull Λ i).map
          ((lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
        towerExchange Λ b i r p w K.obj := by
  let A := ModuleCat.{u + 1} Λ
  let θ := (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (upperStarCompIso A w.symm) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _
  have hc (v : H ⟶ V) (Z : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology H) A)) :
      (towerPull Λ v).map
          ((lowerStar A v).rightDerivedFunctorPlusCompatibility.hom.app Z) ≫
        (towerPullPushAdjunction Λ v).counit.app Z.obj =
      DerivedCategory.Plus.ι.map
        ((derivedUpperStarLowerStarAdjunctionPlus A v).counit.app Z) := by
    dsimp only [derivedUpperStarLowerStarAdjunctionPlus, Adjunction.derivedAdjunctionPlus]
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp]
    rfl
  have hc' (Z : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) A)) :
      (towerPull Λ p).map
          ((lowerStar A p).rightDerivedFunctorPlusCompatibility.hom.app Z) ≫
        (towerPullPushAdjunction Λ p).counit.app Z.obj =
      DerivedCategory.Plus.ι.map
        ((derivedUpperStarLowerStarAdjunctionPlus A p).counit.app Z) := by
    dsimp only [derivedUpperStarLowerStarAdjunctionPlus, Adjunction.derivedAdjunctionPlus]
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp]
    rfl
  have hs (M : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology S) A)) :
      DerivedCategory.Plus.ι.map (θ.hom.app M) =
        (towerPullSquare Λ b i r p w).hom.app M.obj := by
    have hinv := inclusion_comp_inv (upperStar A i) (upperStar A r) M
    simp only [θ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app, hinv]
    rfl
  have ht := towerSiteMate_transport
    (derivedUpperStarLowerStarAdjunctionPlus A p)
    (derivedUpperStarLowerStarAdjunctionPlus A r)
    (towerPullPushAdjunction Λ p) (towerPullPushAdjunction Λ r)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (lowerStar A p).rightDerivedFunctorPlusCompatibility.hom
    (lowerStar A r).rightDerivedFunctorPlusCompatibility.hom
    θ.hom (towerPullSquare Λ b i r p w).hom
    (by intro Z; simpa only [Iso.refl_hom, NatTrans.id_app, Category.id_comp,
      Functor.comp_obj, ObjectProperty.ι_obj] using hc' Z)
    (by intro Z; simpa only [Iso.refl_hom, NatTrans.id_app, Category.id_comp,
      Functor.comp_obj, ObjectProperty.ι_obj] using hc r Z)
    (by
      intro M
      simp only [Iso.refl_hom, NatTrans.id_app]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      dsimp only [Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj]
      simp only [Category.comp_id, Category.id_comp]
      exact hs M) K
  simp only [towerPlusExchange, θ, towerExchange, mateEquiv_apply, TwoSquare.mk,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Functor.comp_map,
    Functor.comp_obj, Functor.map_comp, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Category.id_comp, Category.assoc, CategoryTheory.Functor.map_id,
    ObjectProperty.ι_obj] at ht ⊢
  dsimp only [Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj] at ht ⊢
  erw [CategoryTheory.Functor.map_id] at ht ⊢
  simp only [Category.id_comp, Category.comp_id] at ht ⊢
  exact ht

private theorem tower_site_inverse_unit [Finite Λ] {H T : Scheme.{u}}
    (b : H ⟶ T) [IsOpenImmersion b]
    (E : DerivedCategory.Plus (Sheaf H.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (upperStar (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.map
        ((properOpenSiteExtensionIso Λ b).hom.app E) ≫
      inv ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) b).unit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) H).mapDerivedCategoryPlus.obj E)) =
    (fixedComparisonPullbackPlus Λ b).inv.app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.obj E) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) H).mapDerivedCategoryPlus.map
        (inv ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} Λ) b).unit.app E)) := by
  have h := plus_unit Λ b E
  dsimp only at h
  apply (cancel_epi ((comparisonUpperStar (ModuleCat.{u + 1} Λ) H).mapDerivedCategoryPlus.map
      ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) b).unit.app E) ≫
      (fixedComparisonPullbackPlus Λ b).hom.app _)).mp
  simp only [Category.assoc]
  dsimp only [derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus,
    Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus] at h ⊢
  rw [reassoc_of% h]
  simp only [IsIso.hom_inv_id, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  rfl

private theorem tower_etale_restriction_hom [Finite Λ]
    {H T V S : Scheme.{u}}
    [IsNoetherian H] [IsNoetherian T] [IsNoetherian V] [IsNoetherian S]
    {b : H ⟶ T} {i : V ⟶ S} {r : H ⟶ V} {p : T ⟶ S}
    [IsOpenImmersion b] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback b r p i)
    (E : DerivedCategory (Sheaf H.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.properOpenCoefficientRestriction Λ sq).hom.app E =
      (Etale.exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} Λ) b).mapDerivedCategory.obj E) ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctor.map
          (inv ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} Λ) b).unit.app E)) := by
  obtain ⟨lam, hl, hg⟩ :=
    (Etale.properOpenCoefficientInterchange_normalized_exists Λ sq).choose_spec
  have he : ((Etale.properOpenCoefficientRestriction Λ sq).app E).symm =
      (lam.app E).symm := by
    apply Iso.ext
    change (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) i).homEquiv _ _
        ((Etale.properOpenCoefficientInterchange Λ sq).hom.app E) = lam.inv.app E
    rw [show (Etale.properOpenCoefficientInterchange Λ sq).hom.app E = _ from hg E]
    exact Equiv.apply_symm_apply _ _
  have hh := congrArg Iso.inv he
  exact hh.trans (hl E)

private theorem tower_etale_restrictionPlus_hom [Finite Λ]
    {H T V S : Scheme.{u}}
    [IsNoetherian H] [IsNoetherian T] [IsNoetherian V] [IsNoetherian S]
    {b : H ⟶ T} {i : V ⟶ S} {r : H ⟶ V} {p : T ⟶ S}
    [IsOpenImmersion b] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback b r p i)
    (E : DerivedCategory.Plus (Sheaf H.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.properOpenCoefficientRestrictionPlus Λ sq E).hom =
      (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.obj E) ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.map
          (inv ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
            (ModuleCat.{u + 1} Λ) b).unit.app E)) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Etale.properOpenCoefficientRestrictionPlus, Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc, tower_etale_restriction_hom]
  have he := Etale.exact_exchange_plus (ModuleCat.{u + 1} Λ) sq.toCommSq
    ((Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.obj E)
  rw [← Etale.baseChange_eq_derivedBaseChangeMapPlus] at he
  simp only [Etale.properOpenCoefficientTargetPlus, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  dsimp only [Functor.comp_obj] at he ⊢
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [he]
  have hu : DerivedCategory.Plus.ι.map
      ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) b).unit.app E) =
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) b).unit.app E.obj := by
    exact Etale.open_unit_plus (ModuleCat.{u + 1} Λ) b E
  have hui : DerivedCategory.Plus.ι.map
      (inv ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) b).unit.app E)) =
    inv ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) b).unit.app E.obj) := by
    rw [Functor.map_inv]
    exact IsIso.inv_eq_inv.mpr hu
  have hn :=
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusCompatibility.hom.naturality
    (inv ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) b).unit.app E))
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← hui, ← reassoc_of% hn]
  simp only [Iso.hom_inv_id_app, Category.comp_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id, Category.id_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id]
  dsimp only [Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj]
  simp only [Category.comp_id]

attribute [local irreducible] upperStarLowerStarAdjunction
  openImmersionLowerShriekUpperStarAdjunction
  Etale.upperStarLowerStarAdjunction Etale.openImmersionLowerShriekUpperStarAdjunction

private theorem tower_site_lambda [Finite Λ]
    {H T V S : Scheme.{u}}
    [IsNoetherian H] [IsNoetherian T] [IsNoetherian V] [IsNoetherian S]
    {b : H ⟶ T} {i : V ⟶ S} {r : H ⟶ V} {p : T ⟶ S}
    [IsOpenImmersion b] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback b r p i)
    (E : DerivedCategory.Plus (Sheaf H.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    towerPlusLambda Λ b i r p sq.w
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) H).mapDerivedCategoryPlus.obj E) =
      (properOpenSiteRestrictionInverse Λ sq E).inv := by
  letI := isIso_fixedComparisonDirectImageMatePlus Λ p
  letI := isIso_fixedComparisonDirectImageMatePlus Λ r
  let C := (comparisonUpperStar (ModuleCat.{u + 1} Λ) H).mapDerivedCategoryPlus
  let P := (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus
  let R := (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus
  let I := (upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus
  let B := (upperStar (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus
  let JE := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus
  let t := (asIso (fixedComparisonDirectImageMatePlus Λ p)).app (JE.obj E) ≪≫
    P.mapIso ((properOpenSiteExtensionIso Λ b).app E)
  have hn := (towerPlusExchange Λ b i r p sq.w).naturality
    ((properOpenSiteExtensionIso Λ b).hom.app E)
  dsimp only [Functor.comp_map] at hn
  have hf := compactSupportProperFactor Λ sq.flip (JE.obj E)
  have hu := tower_site_inverse_unit Λ b E
  apply (cancel_epi (I.map t.hom)).mp
  unfold towerPlusLambda
  dsimp only [t, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← R.map_comp]
  rw [hu, R.map_comp]
  rw [reassoc_of% hf]
  have hr := (fixedComparisonDirectImageMatePlus Λ r).naturality
    (inv ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) b).unit.app E))
  dsimp only [Functor.comp_map] at hr
  dsimp only [R, JE, Functor.comp_obj] at hr ⊢
  erw [← hr]
  rw [← Functor.map_comp_assoc]
  erw [← tower_etale_restrictionPlus_hom Λ sq E]
  simp only [properOpenSiteRestrictionInverse, Iso.trans_inv, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_inv, asIso_hom, asIso_inv,
    Functor.map_comp, Category.assoc]
  dsimp only [I, P, Functor.comp_obj, Functor.id_obj]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [(lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus.map_id,
    Category.id_comp]
  have hd := congr_app (IsIso.hom_inv_id (fixedComparisonDirectImageMatePlus Λ p))
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.obj E)
  dsimp only [NatTrans.comp_app, NatTrans.id_app] at hd
  rw [hd]
  erw [(upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map_id, Category.id_comp]
  rfl

private theorem tower_exact_unit {C D : Type (u + 2)}
    [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D]
    [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
    [IsGrothendieckAbelian C] [IsGrothendieckAbelian D]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [CategoryTheory.Abelian.HasFunctorialFlatResolution C]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) [IsIso a.unit] :
    ((Functor.mapDerivedCategoryIdIso C).inv ≫
      (Functor.mapDerivedCategoryNatIso (asIso a.unit)).hom ≫
      (Functor.mapDerivedCategoryCompIso F G).inv) = a.mapDerivedCategoryAdjunction.unit := by
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ))
  intro K
  rw [← cancel_mono (G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
    G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryNatIso_fach,
    ← Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj, Iso.inv_hom_id_app_assoc,
    a.mapDerivedCategoryAdjunction_unit_app_fac]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  change (HomotopyCategory.quotient C (.up ℤ)).map _ =
    (HomotopyCategory.quotient C (.up ℤ)).map _
  congr 1

private theorem tower_open_unit
    {X Y : Scheme.{u}} (b : X ⟶ Y) [IsOpenImmersion b] :
    (towerOpenUnit Λ b).hom =
      (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryAdjunction.unit := by
  exact tower_exact_unit _ _
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) b)

private theorem tower_open_unit_plus {X Y : Scheme.{u}} (b : X ⟶ Y)
    [IsOpenImmersion b]
    (N : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.Plus.ι.map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} Λ) b).unit.app N) =
      (towerOpenUnit Λ b).hom.app N.obj := by
  rw [tower_open_unit]
  dsimp only [derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus,
    Adjunction.mapDerivedCategoryPlusAdjunction]
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom,
    Iso.refl_inv, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

private theorem tower_lambda_plus {H T V S : Scheme.{u}}
    (b : H ⟶ T) (i : V ⟶ S) (r : H ⟶ V) (p : T ⟶ S)
    [IsOpenImmersion b] (w : b ≫ p = r ≫ i)
    (N : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology H) (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.Plus.ι.map (towerPlusLambda Λ b i r p w N) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusCompatibility.hom.app N =
      (towerPull Λ i).map
          ((lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusCompatibility.hom.app
            ((openImmersionLowerShriek
              (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.obj N)) ≫
        towerLambda Λ b i r p w N.obj := by
  have hn :=
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusCompatibility.hom.naturality
    (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) b).unit.app N))
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  have hu : DerivedCategory.Plus.ι.map
      (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) b).unit.app N)) = (towerOpenUnit Λ b).inv.app N.obj := by
    have he : DerivedCategory.Plus.ι.mapIso
        (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} Λ) b).unit.app N)) = (towerOpenUnit Λ b).app N.obj := by
      apply Iso.ext
      exact tower_open_unit_plus Λ b N
    exact congrArg Iso.inv he
  simp only [towerPlusLambda, towerLambda, Functor.map_comp, Category.assoc]
  rw [hn, hu, ← Category.assoc]
  erw [tower_exchange_plus]
  rw [Category.assoc]
  rfl

private theorem tower_gamma_plus [Finite Λ]
    {H T V S : Scheme.{u}}
    [IsNoetherian H] [IsNoetherian T] [IsNoetherian V] [IsNoetherian S]
    {b : H ⟶ T} {i : V ⟶ S} {r : H ⟶ V} {p : T ⟶ S}
    [IsOpenImmersion b] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback b r p i)
    (E : DerivedCategory.Plus (Sheaf H.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hLambda : IsIso (towerLambda Λ b i r p sq.w
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) H).mapDerivedCategory.obj E.obj))) :
    DerivedCategory.Plus.ι.map (properOpenSiteInterchange Λ sq E) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusCompatibility.hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) H).mapDerivedCategoryPlus.obj E)) =
      (towerJ Λ i).map
          ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusCompatibility.hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) H).mapDerivedCategoryPlus.obj E)) ≫
        towerGamma Λ b i r p sq.w _ hLambda := by
  let N := (comparisonUpperStar (ModuleCat.{u + 1} Λ) H).mapDerivedCategoryPlus.obj E
  haveI : IsIso (towerLambda Λ b i r p sq.w N.obj) := hLambda
  let cp := (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusCompatibility
  let cr := (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusCompatibility
  have hl := tower_lambda_plus Λ b i r p sq.w N
  rw [tower_site_lambda Λ sq E] at hl
  have hinv : DerivedCategory.Plus.ι.map (properOpenSiteRestrictionInverse Λ sq E).hom ≫
      (towerPull Λ i).map (cp.hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.obj N)) =
      cr.hom.app N ≫ inv (towerLambda Λ b i r p sq.w N.obj) := by
    apply (cancel_mono (towerLambda Λ b i r p sq.w N.obj)).mp
    rw [Category.assoc, ← hl]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
    rfl
  apply (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) i).homEquiv _ _ |>.injective
  have hu := tower_open_unit_plus Λ i
    ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.obj N)
  rw [tower_open_unit] at hu
  change DerivedCategory.Plus.ι.map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) i).unit.app _) =
    (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) i).unit.app _ at hu
  have hn := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) i).unit.naturality (cr.hom.app N)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj, ObjectProperty.ι_obj] at hu
  erw [← hu]
  change DerivedCategory.Plus.ι.map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) i).unit.app _) ≫
      DerivedCategory.Plus.ι.map
        ((upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map
          (properOpenSiteInterchange Λ sq E)) ≫ _ = _
  rw [← Functor.map_comp_assoc]
  change DerivedCategory.Plus.ι.map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) i).homEquiv _ _ (properOpenSiteInterchange Λ sq E)) ≫ _ = _
  rw [properOpenSiteInterchange, Equiv.apply_symm_apply]
  rw [hinv]
  erw [hu]
  erw [← reassoc_of% hn]
  dsimp only [towerGamma]
  congr 1
  exact ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryAdjunction.homEquiv _ _).apply_symm_apply _ |>.symm

private theorem tower_lambda_model_isIso [Finite Λ]
    {H T V S : Scheme.{u}}
    [IsNoetherian H] [IsNoetherian T] [IsNoetherian V] [IsNoetherian S]
    {b : H ⟶ T} {i : V ⟶ S} {r : H ⟶ V} {p : T ⟶ S}
    [IsOpenImmersion b] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback b r p i)
    (E : DerivedCategory.Plus (Sheaf H.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (towerLambda Λ b i r p sq.w
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) H).mapDerivedCategory.obj E.obj)) := by
  let N := (comparisonUpperStar (ModuleCat.{u + 1} Λ) H).mapDerivedCategoryPlus.obj E
  have hl := tower_lambda_plus Λ b i r p sq.w N
  rw [tower_site_lambda Λ sq E] at hl
  haveI : IsIso ((towerPull Λ i).map
      ((lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusCompatibility.hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.obj N)) ≫
      towerLambda Λ b i r p sq.w N.obj) := by
    rw [← hl]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((towerPull Λ i).map
      ((lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusCompatibility.hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.obj N)))
    (towerLambda Λ b i r p sq.w N.obj)

end AlgebraicGeometry.ProEtale
