/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Finite.FiniteSiteWordRefinement
import all WeilConjectures.AlgebraicGeometry.FiniteSiteTower.FiniteSiteTowerPaste
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientMate
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.Compactification.CategoryBaseChange

set_option linter.privateModule false

/-! # Finite-ring compact-support site coherence

Source: Stacks Project, more-etale.tex, Tags 0F7I, 0F7J and 0F7K;
canonical site-square deduction in the DAG
(blueprint: lem-sp-finite-compact-site-coherence).

The tower arrow below uses the specified open adjunct Gamma, not conjugation of
an etale composition arrow. All inputs retain their bounded-below etale witness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local implicit_reducible] AlgebraicGeometry.Etale.derivedPlusFormalism

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local implicit_reducible] Compactification.copy
attribute [local implicit_reducible] coherenceEtaleFunctor
variable (R : Type (u + 1)) [CommRing R] [Finite R]

private def towerEtaleIso
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :
    coherenceEtaleFunctor R T.cf ⋙ coherenceEtaleFunctor R T.cg ≅
      coherenceEtaleFunctor R T.cfg :=
  Etale.native_bounded_triangle_iso (ModuleCat.{u + 1} R) T

private theorem etale_change_trans
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d e : Compactification f) :
    coherenceEtaleChangeIso R c d ≪≫ coherenceEtaleChangeIso R d e =
      coherenceEtaleChangeIso R c e :=
  Etale.rightDerivedLowerShriekOfCompactificationPlusIso_trans R c d e

private theorem compositor_paste
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F F₀ F₁ : A ⥤ B} {G G₀ G₁ : B ⥤ C} {H H₀ H₁ : A ⥤ C}
    (a₀ : F ⟶ F₀) (a₁ : F₀ ⟶ F₁) (b₀ : G ⟶ G₀) (b₁ : G₀ ⟶ G₁)
    (c : F₁ ⋙ G₁ ⟶ H₁) (d₁ : H₁ ⟶ H₀) (d₀ : H₀ ⟶ H)
    (μ : F₀ ⋙ G₀ ⟶ H₀)
    (hm : μ = NatTrans.hcomp a₁ b₁ ≫ c ≫ d₁) (E : A) :
    G.map (a₀.app E) ≫ b₀.app (F₀.obj E) ≫ μ.app E ≫ d₀.app E =
      G.map ((a₀ ≫ a₁).app E) ≫ (b₀ ≫ b₁).app (F₁.obj E) ≫
        c.app E ≫ (d₁ ≫ d₀).app E := by
  rw [hm]
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp, Category.assoc]
  rw [← b₁.naturality_assoc, ← b₀.naturality_assoc]

private theorem compositor_component
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F F' : A ⥤ B) (G G' : B ⥤ C) (H H' : A ⥤ C)
    (a : F ≅ F') (b : G ≅ G') (c : F' ⋙ G' ≅ H) (d : H ≅ H') (E : A) :
    (coherenceCompositorOfChanges F F' G G' H H' a b c d).hom.app E =
      G.map (a.hom.app E) ≫ b.hom.app (F'.obj E) ≫ c.hom.app E ≫ d.hom.app E := by
  rfl

private theorem compositor_iso_paste
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F F₀ F₁ : A ⥤ B} {G G₀ G₁ : B ⥤ C} {H H₀ H₁ : A ⥤ C}
    (a₀ : F ≅ F₀) (a₁ : F₀ ≅ F₁) (b₀ : G ≅ G₀) (b₁ : G₀ ≅ G₁)
    (c : F₁ ⋙ G₁ ≅ H₁) (d₁ : H₁ ≅ H₀) (d₀ : H₀ ≅ H)
    (μ : F₀ ⋙ G₀ ≅ H₀)
    (hm : μ.hom = NatTrans.hcomp a₁.hom b₁.hom ≫ c.hom ≫ d₁.hom) :
    coherenceCompositorOfChanges F F₀ G G₀ H₀ H a₀ b₀ μ d₀ =
      coherenceCompositorOfChanges F F₁ G G₁ H₁ H
        (a₀ ≪≫ a₁) (b₀ ≪≫ b₁) c (d₁ ≪≫ d₀) := by
  apply Iso.ext
  ext E
  simp only [compositor_component, Iso.trans_hom]
  exact compositor_paste a₀.hom a₁.hom b₀.hom b₁.hom c.hom d₁.hom d₀.hom μ.hom hm E

-- Avoid unfolding whole derived functors when normalizing the compositor.
set_option backward.isDefEq.respectTransparency false in
private theorem etale_compositor_tower
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (coherenceEtaleCompositor R c d e).hom.app E =
      (coherenceEtaleFunctor R d).map
        ((coherenceEtaleChangeIso R c T.cf).hom.app E) ≫
      (coherenceEtaleChangeIso R d T.cg).hom.app ((coherenceEtaleFunctor R T.cf).obj E) ≫
      (towerEtaleIso R T).hom.app E ≫
      (coherenceEtaleChangeIso R T.cfg e).hom.app E := by
  let := c.hasCompactification
  let := d.hasCompactification
  let := e.hasCompactification
  have h : (coherenceChosenEtaleCompositorIso R f g).hom =
      NatTrans.hcomp
        (coherenceEtaleChangeIso R (HasCompactification.compactification f) T.cf).hom
        (coherenceEtaleChangeIso R (HasCompactification.compactification g) T.cg).hom ≫
      (towerEtaleIso R T).hom ≫
      (coherenceEtaleChangeIso R T.cfg
        (HasCompactification.compactification (f ≫ g))).hom := by
    exact Etale.compositor_middle_transport _ _ _ _
      (congrArg Iso.hom
        (Etale.native_bounded_triangle_iso_eq (ModuleCat.{u + 1} R) T).symm)
      (Etale.rightDerivedLowerShriekPlusCompIso_hom_eq R T)
  have hp := compositor_iso_paste
    (F := coherenceEtaleFunctor R c)
    (F₀ := coherenceEtaleFunctor R (HasCompactification.compactification f))
    (F₁ := coherenceEtaleFunctor R T.cf)
    (G := coherenceEtaleFunctor R d)
    (G₀ := coherenceEtaleFunctor R (HasCompactification.compactification g))
    (G₁ := coherenceEtaleFunctor R T.cg)
    (H := coherenceEtaleFunctor R e)
    (H₀ := coherenceEtaleFunctor R (HasCompactification.compactification (f ≫ g)))
    (H₁ := coherenceEtaleFunctor R T.cfg)
    (coherenceEtaleChangeIso R c (HasCompactification.compactification f))
    (coherenceEtaleChangeIso R (HasCompactification.compactification f) T.cf)
    (coherenceEtaleChangeIso R d (HasCompactification.compactification g))
    (coherenceEtaleChangeIso R (HasCompactification.compactification g) T.cg)
    (towerEtaleIso R T)
    (coherenceEtaleChangeIso R T.cfg (HasCompactification.compactification (f ≫ g)))
    (coherenceEtaleChangeIso R (HasCompactification.compactification (f ≫ g)) e)
    (coherenceChosenEtaleCompositorIso R f g) h
  rw [etale_change_trans, etale_change_trans, etale_change_trans] at hp
  exact (congrArg (fun t ↦ t.hom.app E) hp).trans
    (compositor_component _ _ _ _ _ _ _ _ _ _ E)

section TowerCalculation
attribute [local implicit_reducible] ExchangeFormalism.shriek
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryPlus Functor.mapDerivedCategory
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option maxRecDepth 2048 in
private theorem tower_etale_normalization
    {X U XB Y YB Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian XB]
    [IsNoetherian Y] [IsNoetherian YB] [IsNoetherian Z]
    (a : X ⟶ U) (b : U ⟶ XB) (p : XB ⟶ YB) (q : YB ⟶ Z)
    (i : Y ⟶ YB) (s : U ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion i]
    [QuasiCompact a] [QuasiCompact b] [QuasiCompact i]
    [IsProper p] [IsProper q] [IsProper s]
    (sq : IsPullback b s p i) (E : FiniteSiteTower.DE R X) :
    FiniteSiteTower.AE R a b p q i s sq E =
      (Etale.native_bounded_triangle_iso (ModuleCat.{u + 1} R)
        (FiniteSiteTower.towerTriangle a b p q i s sq)).hom.app E := by
  apply DerivedCategory.Plus.ι.map_injective
  apply (cancel_mono (FiniteSiteTower.targetCompatibility R a b p q E).hom).1
  rw [FiniteSiteTower.etale_normalization, FiniteSiteTower.AEUnbounded_eq_triangle]
  have h := Etale.triangle_comp_plus R (FiniteSiteTower.towerTriangle a b p q i s sq) E
  simp only [FiniteSiteTower.sourceCompatibility, FiniteSiteTower.targetCompatibility,
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Etale.native_unbounded_triangle_iso, FiniteSiteTower.towerTriangle,
    FiniteSiteTower.compactificationF, FiniteSiteTower.compactificationG,
    FiniteSiteTower.compactificationGF, Iso.symm_hom, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id,
    Etale.rightDerivedLowerShriekOfCompactification, Functor.comp_map,
    Functor.map_comp, Category.assoc, FiniteSiteTower.JE, FiniteSiteTower.PE,
    Etale.rightDerivedLowerShriekOfCompactificationPlus, Functor.comp_obj,
    ObjectProperty.ι_obj] at h ⊢
  convert! h.symm using 1

end TowerCalculation

omit [Finite R] in
private theorem etale_proper_id_eq (X : Scheme.{u}) :
    (Etale.derivedPlusFormalism (ModuleCat.{u + 1} R)).pfId X =
      Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} R) X := by
  let a := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) (𝟙 X)).derivedPlus
  let e := Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} R) X
  let r := Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} R) X
  change conjugateIsoEquiv a Adjunction.id e.symm = r
  apply Iso.ext
  apply conjugateEquiv_eq_of_unit
  intro K
  have h := NatTrans.congr_app
    (Etale.derivedPlus_unit_comp_upperStarIdDerivedPlus (ModuleCat.{u + 1} R) X) K
  change a.unit.app K ≫
    (Etale.lowerStar (ModuleCat.{u + 1} R) (𝟙 X)).rightDerivedFunctorPlus.map
      (e.hom.app K) = r.inv.app K at h
  have ht := congrArg (fun t ↦ t ≫
    (Etale.lowerStar (ModuleCat.{u + 1} R) (𝟙 X)).rightDerivedFunctorPlus.map
      (e.inv.app K) ≫ r.hom.app _) h
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at ht
  rw [r.hom.naturality (e.inv.app K)] at ht
  simpa only [Iso.symm_hom, Adjunction.id_unit, NatTrans.id_app, Functor.id_map,
    Functor.id_obj, Category.id_comp, Iso.inv_hom_id_app_assoc] using ht

omit [Finite R] in
private theorem etale_open_id_eq (X : Scheme.{u}) :
    (Etale.derivedPlusFormalism (ModuleCat.{u + 1} R)).shId X =
      finiteSiteEtaleOpenId R X := by
  apply Etale.conjugate_iso_symm_eq
  apply conjugateEquiv_eq_of_unit
  intro K
  apply DerivedCategory.Plus.ι.map_injective
  have hp : DerivedCategory.Plus.ι.mapIso
      ((Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} R) X).app K) =
      (Functor.mapDerivedCategoryNatIso
        (Etale.upperStarId (ModuleCat.{u + 1} R) X) ≪≫
          Functor.mapDerivedCategoryIdIso _).app K.obj := by
    apply Iso.ext
    simp only [Functor.mapIso_hom, Iso.app_hom, Etale.upperStarIdDerivedPlus,
      Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusIdIso_hom_app]
    rfl
  have hi := congrArg Iso.inv hp
  simp only [Functor.mapIso_inv, Iso.app_inv] at hi
  have h := unit_conjugateEquiv Adjunction.id
    (Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} R) (𝟙 X)).mapDerivedCategoryAdjunction
    (Functor.mapDerivedCategoryNatIso
      (Adjunction.leftAdjointIdIso
        (Etale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} R) (𝟙 X))
        (Etale.upperStarId (ModuleCat.{u + 1} R) X)) ≪≫
      Functor.mapDerivedCategoryIdIso _).hom K.obj
  rw [Etale.derived_open_id_conjugate] at h
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj,
    Category.id_comp] at h
  dsimp only [Etale.derivedPlusFormalism, ExchangeFormalism.pb,
    ExchangeFormalism.pbId, ExchangeFormalism.shAdj]
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj,
    Category.id_comp, Iso.symm_hom, Functor.map_comp, Etale.open_unit_plus,
    Etale.exact_map_plus, finiteSiteEtaleOpenId, Iso.trans_hom, NatTrans.comp_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusIdIso_hom_app, hi]
  change (Functor.mapDerivedCategoryNatIso
      (Etale.upperStarId (ModuleCat.{u + 1} R) X) ≪≫
        Functor.mapDerivedCategoryIdIso _).inv.app K.obj =
    (Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} R) (𝟙 X)).mapDerivedCategoryAdjunction.unit.app K.obj ≫
      (Etale.upperStar (ModuleCat.{u + 1} R) (𝟙 X)).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso
          ((Etale.openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} R) (𝟙 X)).leftAdjointIdIso
              (Etale.upperStarId (ModuleCat.{u + 1} R) X))).hom.app K.obj) ≫
      (Etale.upperStar (ModuleCat.{u + 1} R) (𝟙 X)).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryIdIso _).hom.app K.obj)
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] using h

section UnitCalculation
attribute [local implicit_reducible] ExchangeFormalism.shriek
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryPlus Functor.mapDerivedCategory
end UnitCalculation

section AssociativityCalculation
attribute [local implicit_reducible] ExchangeFormalism.shriek
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryPlus Functor.mapDerivedCategory

end AssociativityCalculation

end AlgebraicGeometry.ProEtale
