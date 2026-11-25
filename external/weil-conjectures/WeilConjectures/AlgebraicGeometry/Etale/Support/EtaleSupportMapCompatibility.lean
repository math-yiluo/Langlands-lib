/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteCompactSupportExact
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphTensor
import WeilConjectures.CategoryTheory.Right.RightDerivedSingleH0
import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-!
# Compatibility of the etale proper-support comparison

Source: Stacks Project, Tags 0F4L, 0F4Y, 0GKM, 03S6, 0F7L, 0GKF and 0GL5
(blueprint: lem-pur-etale-support-map-compatibility).

The auxiliary arrows transport the existing derived tensor comparison to the exact
inverse-image functor and take its projection mate under the existing sum adjunction.
The statement characterizes its comparisons by graph extension and the derived unit.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance] derivedBraidedCategory _root_.DerivedCategory.braidedCategory'
attribute [local instance 2000] Sheaf.instHasColimitsOfShape
attribute [local irreducible] Functor.mapDerivedCategory Adjunction.mapDerivedCategoryAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  upperStar lowerStar
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor

/-- Tensor comparison for termwise exact inverse image. This is the existing derived
pullback tensor comparison transported through `L(e^*) ≅ D(e^*)` in both variables.
Source: Stacks Project, Tags 0GKF and 0GL5
(blueprint: lem-pur-etale-support-map-compatibility). -/
noncomputable def etaleSupportExactUpperTensorIso
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (e : V ⟶ T) :
    (((Functor.whiskeringLeft₂ _).obj
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
        (derivedTensor (ModuleCat.{u + 1} A) V) ≅
      (Functor.postcompose₂.obj (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
        (derivedTensor (ModuleCat.{u + 1} A) T) :=
  (((Functor.whiskeringLeft₂ _).mapIso
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm).app
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).app
          (derivedTensor (ModuleCat.{u + 1} A) V) ≪≫
    (((Functor.whiskeringLeft₂ _).obj
      (upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor).mapIso
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm).app
          (derivedTensor (ModuleCat.{u + 1} A) V) ≪≫
    (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) e).symm ≪≫
    (Functor.postcompose₂.mapIso
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e)).app
        (derivedTensor (ModuleCat.{u + 1} A) T)

/-- The reverse sum-extension projection arrow. It is the projection mate of the
sum/evaluation adjunction, using the canonical exact pullback tensor comparison above.
Its inverse is the map `(s,m) ⊗ k ↦ (s,m ⊗ s^*k)` of Tag 0GKF: transposing this rule
sends the summand generator to the unit inclusion tensored with the restricted section.
Thus the normalization below specifies a particular map, not an arbitrary isomorphism.
Source: Stacks Project, Tags 0GKF and 0GL5
(blueprint: lem-pur-etale-support-map-compatibility). -/
noncomputable def etaleSupportSumProjectionReverse
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (e : V ⟶ T) [Etale e] :
    (Functor.postcompose₂.obj
        (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory).obj
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
          (derivedTensor (ModuleCat.{u + 1} A) V)) ⟶
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        derivedTensor (ModuleCat.{u + 1} A) T :=
  ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
      inferInstance).mapDerivedCategoryAdjunction).projectionMap
    (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
    (derivedTensor (ModuleCat.{u + 1} A) V) (derivedTensor (ModuleCat.{u + 1} A) T)
    (etaleSupportExactUpperTensorIso A e).hom

private theorem supportSheafIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
    [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] (c : Compactification e) :
    IsIso (N.sheafComparison e c) := by
  let O := openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i
  let R := lowerStar (ModuleCat.{u + 1} A) c.g
  let H := DerivedCategory.homologyFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0
  let a := N.sheafComparison e c
  have happ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) : IsIso (a.app M) := by
    let P := (HomotopyCategory.singleFunctor _ 0).obj M
    let Z := (O.mapHomotopyCategory (.up ℤ)).obj P
    let b : Z ≅ (HomotopyCategory.singleFunctor _ 0).obj (O.obj M) :=
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex O (.up ℤ) 0).app M)
    have hu₀ : IsIso (H.map (R.singleRightDerivedUnit.app (O.obj M))) := by
      have hh := R.rightDerivedFunctorUnit_homology_zero (O.obj M)
      have : IsIso (H.map (R.singleRightDerivedUnit.app (O.obj M)) ≫
          (R.singleRightDerivedH0Iso (O.obj M)).hom) := by
        rw [hh]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (R.singleRightDerivedH0Iso (O.obj M)).hom
    have hu : IsIso (H.map (R.rightDerivedFunctorUnit.app
        ((HomotopyCategory.singleFunctor _ 0).obj (O.obj M)))) := by
      rw [Functor.singleRightDerivedUnit_app, H.map_comp] at hu₀
      simp only [cast_eq] at hu₀
      exact IsIso.of_isIso_comp_left
        (H.map (DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).inv.app
            (O.obj M)))) _
    have hz : IsIso (H.map (R.rightDerivedFunctorUnit.app Z)) := by
      have hn := congrArg H.map (R.rightDerivedFunctorUnit.naturality b.hom)
      simp only [Functor.comp_map, H.map_comp] at hn
      have : IsIso (H.map (R.rightDerivedFunctorUnit.app Z) ≫
          H.map (R.rightDerivedFunctor.map (DerivedCategory.Qh.map b.hom))) := by
        rw [← hn]
        infer_instance
      exact IsIso.of_isIso_comp_right _
        (H.map (R.rightDerivedFunctor.map (DerivedCategory.Qh.map b.hom)))
    have hall : IsIso (H.map (compactSupportComparisonOnHomotopy A e c a P)) := by
      dsimp only [a]
      rw [← N.derived_normalization]
      infer_instance
    have ha : IsIso (H.map (DerivedCategory.Qh.map
        ((a.mapHomotopyCategory (.up ℤ)).app P))) := by
      simpa only [compactSupportComparisonOnHomotopy, normalizationHomotopyComponent,
        H.map_comp,
        isIso_comp_left_iff, isIso_comp_right_iff] using hall
    have hh : IsIso ((HomotopyCategory.homologyFunctor _ (.up ℤ) 0).map
        ((a.mapHomotopyCategory (.up ℤ)).app P)) :=
      (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactorsh _ 0) _).1 ha
    have hc : IsIso (HomologicalComplex.homologyMap
        ((a.mapHomologicalComplex (.up ℤ)).app
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) 0) :=
      (NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors _ (.up ℤ) 0) _).1 hh
    exact (Arrow.isIso_hom_iff_isIso_hom_of_isIso
      (arrowIsoHomologyMapMapHomologicalComplexSingle _ _ a M).hom).1 hc
  have := happ
  exact NatIso.isIso_of_isIso_app a

private theorem rightProjection_eq_braiding
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D]
    [MonoidalClosed C] [MonoidalClosed D]
    {L : C ⥤ D} {G : D ⥤ C} [G.Monoidal]
    (adj : L ⊣ G)
    (hG : ∀ X Y, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X)
    (M : C) (K : D) :
    L.map (adj.unit.app M ▷ G.obj K ≫ Functor.LaxMonoidal.μ G (L.obj M) K) ≫
        adj.counit.app (L.obj M ⊗ K) =
      L.map (β_ M (G.obj K)).hom ≫
        (Functor.Monoidal.projectionMap adj K).app M ≫ (β_ (L.obj M) K).inv := by
  simp only [Functor.Monoidal.projectionMap, Category.assoc]
  have hn := adj.counit.naturality (β_ (L.obj M) K).inv
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [← hn, ← L.map_comp_assoc, ← L.map_comp_assoc]
  congr 2
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left]
  simp only [Category.assoc]
  have hc := congrArg
    (fun f ↦ adj.unit.app M ▷ G.obj K ≫ f ≫ G.map (β_ (L.obj M) K).inv)
    (hG (L.obj M) K)
  simpa only [Functor.comp_obj, Category.assoc, ← G.map_comp, Iso.hom_inv_id,
    G.map_id, asIso_hom, Category.comp_id] using hc

private theorem braided_transport
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D]
    {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G)
    (hF : ∀ X Y, Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X) :
    let _ := Functor.Monoidal.transport i
    ∀ X Y, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X := by
  let _ := Functor.Monoidal.transport i
  dsimp only
  intro X Y
  simp only [Functor.Monoidal.transport_μ, Category.assoc]
  rw [← i.hom.naturality]
  rw [reassoc_of% (hF X Y)]
  rw [BraidedCategory.braiding_naturality_assoc]

private theorem transport_tensorator
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G)
    (α : (Functor.postcompose₂.obj F).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor D))
    (hα : ∀ X Y, ((α.inv.app X).app Y) = Functor.LaxMonoidal.μ F X Y) :
    let _ := Functor.Monoidal.transport i
    ∀ X Y, (((((Functor.whiskeringLeft₂ _).mapIso i.symm).app G).app
        (curriedTensor D) ≪≫
      (((Functor.whiskeringLeft₂ _).obj F).mapIso i.symm).app (curriedTensor D) ≪≫
      α.symm ≪≫ (Functor.postcompose₂.mapIso i).app (curriedTensor C)).hom.app X).app Y =
        Functor.LaxMonoidal.μ G X Y := by
  let _ := Functor.Monoidal.transport i
  dsimp only
  intro X Y
  rw [Functor.Monoidal.transport_μ i X Y, ← hα X Y]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  rfl

private theorem supportProjectionIsoGeneral
    (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    [HasSmallSiteSheafify D] {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    [(upperStar D e).PreservesFlat]
    [∀ M : D, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]
    [(V.smallEtaleTopology.W (A := D)).IsMonoidal]
    [(T.smallEtaleTopology.W (A := D)).IsMonoidal]
    (θ : (((Functor.whiskeringLeft₂ _).obj
      (upperStar D e).mapDerivedCategory).obj
        (upperStar D e).mapDerivedCategory).obj (derivedTensor D V) ≅
      (Functor.postcompose₂.obj (upperStar D e).mapDerivedCategory).obj (derivedTensor D T))
    (hθ : θ =
      (((Functor.whiskeringLeft₂ _).mapIso
        (leftDerivedUpperStarIsoMapDerivedCategory D e).symm).app
          (upperStar D e).mapDerivedCategory).app (derivedTensor D V) ≪≫
        (((Functor.whiskeringLeft₂ _).obj
          (upperStar D e).leftDerivedFunctor).mapIso
            (leftDerivedUpperStarIsoMapDerivedCategory D e).symm).app (derivedTensor D V) ≪≫
        (leftDerivedUpperStarTensorNatIso D e).symm ≪≫
        (Functor.postcompose₂.mapIso
          (leftDerivedUpperStarIsoMapDerivedCategory D e)).app (derivedTensor D T)) :
    IsIso (Adjunction.projectionMap
      ((etaleLowerShriekUpperStarAdjunction D e inferInstance).mapDerivedCategoryAdjunction)
      (upperStar D e).mapDerivedCategory (derivedTensor D V) (derivedTensor D T) θ.hom) := by
  let G₀ := (upperStar D e).leftDerivedFunctor
  let G := (upperStar D e).mapDerivedCategory
  let L := (etaleLowerShriek D e inferInstance).mapDerivedCategory
  let i : G₀ ≅ G := leftDerivedUpperStarIsoMapDerivedCategory D e
  let := leftDerivedUpperStarMonoidal D e
  let : G.Monoidal := Functor.Monoidal.transport i
  have : i.hom.IsMonoidal := Functor.Monoidal.natTransIsMonoidal_of_transport i
  let adj : L ⊣ G :=
    (etaleLowerShriekUpperStarAdjunction D e
      inferInstance).mapDerivedCategoryAdjunction
  have hpf (K) : IsIso (Functor.Monoidal.projectionMap adj K) := by
    have := isIso_projectionMap_derivedEtaleLowerShriek
      (A := D) e K
    have : IsIso (Functor.LaxMonoidal.ihomComparison G₀ K) :=
      Functor.Monoidal.isIso_ihomComparison_of_isIso_projectionMap
        (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction e) K
    have : i.symm.hom.IsMonoidal := inferInstanceAs i.inv.IsMonoidal
    have : IsIso (Functor.LaxMonoidal.ihomComparison G K) :=
      Functor.LaxMonoidal.isIso_ihomComparison_of_iso i.symm K
    exact Functor.Monoidal.isIso_projectionMap_of_isIso_ihomComparison adj K
  have hb := braided_transport i
    (leftDerivedUpperStar_μ_map_braiding_hom D e)
  have hμ (X Y) : Functor.LaxMonoidal.μ G₀ X Y =
      ((leftDerivedUpperStarTensorNatIso D e).inv.app X).app Y := by
    apply (cancel_mono
      (((leftDerivedUpperStarTensorNatIso D e).hom.app X).app Y)).1
    change Functor.LaxMonoidal.μ G₀ X Y ≫ Functor.OplaxMonoidal.δ G₀ X Y = _
    rw [Functor.Monoidal.μ_δ, Iso.inv_hom_id_app_app]
    rfl
  have hδ (X Y) : (θ.hom.app X).app Y =
      Functor.LaxMonoidal.μ G X Y := by
    rw [hθ]
    exact transport_tensorator i
      (leftDerivedUpperStarTensorNatIso D e)
      (fun X Y ↦ (hμ X Y).symm) X Y
  have happ (M K) : IsIso
      (((adj.projectionMap G (derivedTensor D V) (derivedTensor D T) θ.hom).app M).app K) := by
    change IsIso (L.map (adj.unit.app M ▷ G.obj K ≫
      (θ.hom.app (L.obj M)).app K) ≫
        adj.counit.app (L.obj M ⊗ K))
    rw [hδ, rightProjection_eq_braiding adj hb]
    have := hpf K
    infer_instance
  have happ₁ M : IsIso
      ((adj.projectionMap G (derivedTensor D V) (derivedTensor D T) θ.hom).app M) := by
    have := happ M
    exact NatIso.isIso_of_isIso_app _
  have := happ₁
  exact NatIso.isIso_of_isIso_app _

private theorem supportProjectionIso
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}}
    (e : V ⟶ T) [Etale e] :
    IsIso (etaleSupportSumProjectionReverse A e) :=
  supportProjectionIsoGeneral (ModuleCat.{u + 1} A) e
    (etaleSupportExactUpperTensorIso A e) rfl

private theorem projection_transpose
    {C D : Type*} [Category C] [Category D]
    {P : C ⥤ D} {R : D ⥤ C} (adj : P ⊣ R)
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (δ : (Functor.postcompose₂.obj P).obj T ⟶
      (((Functor.whiskeringLeft₂ _).obj P).obj P).obj T')
    {A B K : C} {J J' : D}
    (q : A ⟶ (T.obj B).obj K) (t : B ⟶ R.obj J)
    (γ : (T'.obj J).obj (P.obj K) ⟶ J') :
    (adj.homEquiv _ _).symm
      (q ≫ (T.map t).app K ≫
        ((adj.rightAdjointProjectionMap δ).app J).app K ≫ R.map γ) =
      P.map q ≫ (δ.app B).app K ≫
        (T'.map ((adj.homEquiv _ _).symm t)).app (P.obj K) ≫ γ := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hγ := adj.counit.naturality γ
  simp only [Functor.comp_map, Functor.id_map] at hγ
  rw [hγ]
  have hπ := adj.map_rightAdjointProjectionMap_app_app_comp_counit δ J K
  change P.map (((adj.rightAdjointProjectionMap δ).app J).app K) ≫
    adj.counit.app ((T'.obj J).obj (P.obj K)) =
      (δ.app (R.obj J)).app K ≫ (T'.map (adj.counit.app J)).app (P.obj K) at hπ
  rw [reassoc_of% hπ]
  have hn := NatTrans.congr_app (δ.naturality t) K
  change P.map ((T.map t).app K) ≫ (δ.app (R.obj J)).app K =
    (δ.app B).app K ≫ (T'.map (P.map t)).app (P.obj K) at hn
  rw [reassoc_of% hn]
  simp only [NatTrans.comp_app, Category.assoc]

private theorem supportProjectionCompatibility
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
    [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e)
    (M : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).map
            ((leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} A) e).hom.app K)) ≫
        (N.comparison e c).hom.app (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) ≫
        ((etaleSupportSumProjectionReverse A e).app M).app K =
      ((derivedTensor (ModuleCat.{u + 1} A) T).map
        ((N.comparison e c).hom.app M)).app K := by
  let O := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let R := (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor
  let E := (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
  let S := (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
  let T₀ := derivedTensor (ModuleCat.{u + 1} A) T
  let V₀ := derivedTensor (ModuleCat.{u + 1} A) V
  let t := (N.comparison e c).inv
  let q := ((etaleSupportSumProjectionReverse A e).app M).app K
  let γ := ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A) c.i).inv.app M).app
      ((upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K) ≫
    O.map ((V₀.obj M).map
      ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app K)) ≫
    O.map ((V₀.obj M).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app K))
  let sumAdj := (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
    inferInstance).mapDerivedCategoryAdjunction
  have hq : sumAdj.unit.app _ ≫ E.map q =
      (V₀.map (sumAdj.unit.app M)).app (E.obj K) ≫
        (etaleSumExtensionTensorPullbackIso A e (S.obj M) K).hom := by
    exact sumAdj.unit_app_comp_map_projectionMap_app_app E V₀ T₀
      (etaleSupportExactUpperTensorIso A e).hom M K
  have hgraph := compactSupportGraph_tensor_evaluation A N e c M K q hq
  change (upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.map q ≫
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) c.g).app (S.obj M)).app K ≫
      ((derivedTensor (ModuleCat.{u + 1} A) c.Z).map
        (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g).homEquiv _ _).symm
          (t.app M))).app ((upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K) ≫ γ =
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g).homEquiv _ _).symm
      (t.app ((V₀.obj M).obj (E.obj K))) at hgraph
  have hc : q ≫ (T₀.map (t.app M)).app K ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((V₀.obj M).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app K)) =
      t.app ((V₀.obj M).obj (E.obj K)) := by
    apply ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) c.g).homEquiv _ _).symm.injective
    have ht := projection_transpose
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
      T₀ (derivedTensor (ModuleCat.{u + 1} A) c.Z)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) c.g) q (t.app M) γ
    apply Eq.trans _ hgraph
    convert ht using 1
    simp only [projectionMapOfCompactification_app_app, Functor.comp_map,
      Functor.map_comp, Category.assoc, γ]
    rfl
  have := supportProjectionIso A e
  apply (cancel_epi (q ≫ (T₀.map (t.app M)).app K)).1
  simp only [Category.assoc]
  erw [reassoc_of% hc]
  dsimp only [t]
  rw [Iso.inv_hom_id_app_assoc]
  have ht : (T₀.map ((N.comparison e c).inv.app M)).app K ≫
      (T₀.map ((N.comparison e c).hom.app M)).app K = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← T₀.map_comp, Iso.inv_hom_id_app,
      T₀.map_id, NatTrans.id_app]
  change q = q ≫ _
  rw [ht]
  exact (Category.comp_id q).symm

private theorem supportRefinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
    [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (c d : Compactification e) (r : c.Refinement d) :
    (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
      (N.comparison e d).hom = (N.comparison e c).hom := by
  have : IsNoetherian V := ⟨⟩
  have : IsNoetherian T := ⟨⟩
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have h := N.refinement e c d r
  have hr := unboundedEtaleCompactSupport_refinement_normalization A e r N
  have hc := unboundedEtaleCompactSupport_comparison_coherence A e
  have hdc : (rightDerivedLowerShriekOfCompactificationIso A d c).hom ≫
      (N.comparison e c).hom = (N.comparison e d).hom := by
    rw [hr]
    dsimp only [unboundedEtaleRefinementOpenComparison, Iso.symm_hom]
    simpa only [Category.assoc] using h
  rw [← hdc, ← Category.assoc]
  have hi : (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
      (rightDerivedLowerShriekOfCompactificationIso A d c).hom = 𝟙 _ := by
    have hcd := congrArg Iso.hom ((hc.2 c d c).trans (hc.1 c))
    exact hcd
  rw [hi, Category.id_comp]

/-- The canonical proper-support comparison for separated etale finite-type maps
intertwines the specified exchange and projection transformations, on the entire unbounded
categories and for every compactification. The existential families are characterized by
sheaf and homotopy normalization equations; they are not unconstrained comparisons.
The final equation is the compatibility with proper-refinement identifications.

Source: Stacks Project, Tags 0F4L, 0F4Y, 0GKM, 03S6, 0F7L, 0GKF and 0GL5
(blueprint: lem-pur-etale-support-map-compatibility).

Proof:
1. In each compactification the graph of a lift is open and closed: it is open by
   etaleness and closed as a section of the separated proper morphism. Extend the input
   section by zero on its complement and sheafify the sum-presheaf map. The proper-support
   identification of lem-sfb-quasifinite-compact-support-exact makes this an isomorphism.
2. Apply this sheaf map degreewise, followed by the total-derived direct-image unit.
   On a K-injective resolution j_!P → I its transpose is represented by
   I composed with the sheaf counit after pullback of the graph map. Naturality of the
   counit and localization show that this is the descended evaluation map on all P.
3. The inverse of the specified conjugate sum-extension base-change map pulls a sheet
   section to its pulled-back sheet section. This is checked from its unit, ordinary
   exchange and counit, using the restriction/unit formulas. Inverse-image sections are
   only locally represented by source sections; no descent of all lifts is asserted.
   Graph extension commutes with pullback, giving equality of the two evaluation maps.
4. Transpose the exchange identity under r'^* ⊣ Rr'_*. The defining proper-exchange
   mate equation identifies its left side with the first evaluation map in step 3 and
   its right side with the second. The adjunction bijection proves the equality.
5. The sum projection sends (s,m) ⊗ k to (s,m ⊗ s^*k). Its inverse is the projection
   mate defined above, as follows by transposing the sum inclusion on each generator.
   Stalks identify it with distribution of tensor over sums, hence an isomorphism.
   Exact sum extension preserves flat and K-flat complexes by this same formula and
   commutes with sum totalization. Use flat K-flat representatives separately on the
   two sites and descend first in one variable and then in the other.
6. Evaluate on graph-supported tensor generators. Both evaluation composites are
   m ⊗ s^*k on the graph and zero off it. The sheaf axiom, linearity and sheafification
   give equality. On total tensor complexes the differentials have identical signs.
   K-flat tensor descent and localization give equality on the full derived categories.
7. Transpose the projection identity under r^* ⊣ Rr_*. The counit definition of the
   proper projection map gives the first evaluation composite in step 6 and naturality
   gives the second. The adjunction bijection and cancellation of the comparison prove
   the identity. The displayed L(e^*) to D(e^*) transport only records exactness.
8. The proper-refinement identity of lem-sfb-quasifinite-compact-support-exact follows
   from the same graph sections and derived units. Substitute it into the two identities
   to obtain their compatibility with each refinement, including nonfinite proper parts.
-/
theorem etaleSupportMapCompatibility
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∃ (a : ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
        (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
        (c : Compactification e),
        etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⟶
          openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
            lowerStar (ModuleCat.{u + 1} A) c.g),
      ∃ (n : ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
          (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
          (c : Compactification e),
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
            (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory),
        ∃ (p : ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
            (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e],
            (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
                derivedTensor (ModuleCat.{u + 1} A) T ≅
              (Functor.postcompose₂.obj
                (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory).obj
                ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
                  (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
                    (derivedTensor (ModuleCat.{u + 1} A) V))),
          (∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
            (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
            (c : Compactification e),
            IsIso (a e c) ∧
              (∀ M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
                (a e c).app M ≫ (compactificationSheafToDirectImage A c).app M =
                  etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M) ∧
              (∀ P : HomotopyCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
                  (ComplexShape.up ℤ),
                (n e c).inv.app (DerivedCategory.Qh.obj P) =
                  compactSupportComparisonOnHomotopy A e c (a e c) P)) ∧
          (∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
            (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e],
            (p e).inv = etaleSupportSumProjectionReverse A e) ∧
          (∀ {V T T' : Scheme.{u}}
            [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T] [IsLocallyNoetherian T'] [CompactSpace T']
            (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
            (c : Compactification e) (g : T' ⟶ T),
            exactCompactSupportExchange A c g ≫
                Functor.whiskerLeft
                  (upperStar (ModuleCat.{u + 1} A) (pullback.snd g e)).mapDerivedCategory
                  (n (pullback.fst g e)
                    (c.ofIsPullback (IsPullback.of_hasPullback g e).flip)).hom =
              Functor.whiskerRight (n e c).hom
                  (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≫
                (exactEtaleSumExchange A e g).hom) ∧
          (∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
            (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
            (c : Compactification e)
            (M : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
            (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))),
            ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
                (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
                  (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).map
                    ((leftDerivedUpperStarIsoMapDerivedCategory
                      (ModuleCat.{u + 1} A) e).hom.app K)) ≫
                (n e c).hom.app (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
                  ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) =
              ((derivedTensor (ModuleCat.{u + 1} A) T).map ((n e c).hom.app M)).app K ≫
                ((p e).hom.app M).app K) ∧
          (∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
            (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
            (c d : Compactification e) (_r : c.Refinement d),
            (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫ (n e d).hom =
              (n e c).hom) := by
  classical
  obtain ⟨N⟩ := nonempty_etaleCompactSupportNormalization A
  have hp {V T : Scheme.{u}} (e : V ⟶ T) [Etale e] :
      IsIso (etaleSupportSumProjectionReverse A e) := supportProjectionIso A e
  refine ⟨(fun e _ _ _ _ c => N.sheafComparison e c),
    (fun e _ _ _ _ c => N.comparison e c),
    (fun e _ _ _ _ => (asIso (etaleSupportSumProjectionReverse A e)).symm), ?_, ?_, ?_, ?_, ?_⟩
  · intro V T _ _ _ _ e _ _ _ _ c
    exact ⟨supportSheafIso A N e c, N.sheaf_normalization e c,
      N.derived_normalization e c⟩
  · intro V T _ _ _ _ e _ _ _ _
    rfl
  · intro V T T' _ _ _ _ _ _ e _ _ _ _ c g
    exact N.base_change e c g
  · intro V T _ _ _ _ e _ _ _ _ c M K
    have hc := supportProjectionCompatibility A N e c M K
    let i := ((asIso (etaleSupportSumProjectionReverse A e)).app M).app K
    apply (i.eq_comp_inv).2
    have hi : i.hom = ((etaleSupportSumProjectionReverse A e).app M).app K := rfl
    rw [hi]
    simpa only [Category.assoc] using hc
  · intro V T _ _ _ _ e _ _ _ _ c d r
    exact supportRefinement A N e c d r

end AlgebraicGeometry.Etale
