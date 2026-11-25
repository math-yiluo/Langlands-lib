/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.RightDerivedBaseChangeZeroUnit
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Unbounded exchange agrees with bounded exchange and with degree-zero exchange

Source: blueprint, chap-Smooth-purity, proposition-ordinary-external-kunneth--1,
node lem-kun-unbounded-exchange-agrees; Stacks Project, Tags 07A7 and 05TD(3)
(blueprint: lem-kun-unbounded-exchange-agrees).

The endpoint isomorphisms below are composites of the fixed exact-functor cohomology
comparison, the single-object right-derived comparison, and the degree-zero comparison.
The last two are induced by augmentations into nonnegative injective resolutions.
-/

@[expose] public section
set_option linter.privateModule false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private lemma inclusion_exact_map
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {K L : DerivedCategory.Plus C} (q : K ⟶ L) :
    DerivedCategory.Plus.ι.map (G.mapDerivedCategoryPlus.map q) =
      G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map q) := rfl

private lemma mate_app
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
    {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (θ : G ⋙ L' ⟶ L ⋙ G') (K : C₁) :
    (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ θ)).app K =
      adj'.unit.app (G.obj (R.obj K)) ≫ R'.map (θ.app (R.obj K)) ≫
        R'.map (G'.map (adj.counit.app K)) := by
  simp [mateEquiv_apply]

section

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
  [Abelian.HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private lemma plus_comparison_unit (F : D ⥤ C) [F.Additive]
    (K : HomotopyCategory.Plus D) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app K) ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
      F.rightDerivedFunctorUnit.app K.obj := by
  simpa only [Functor.comp_obj, ObjectProperty.ι_obj,
    Functor.rightDerivedFunctorPlusCompatibility,
    Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
    Functor.rightDerivedFunctorPlusιUnit, Functor.ιRightDerivedFunctorUnit,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.id_app,
    Iso.refl_hom, Category.id_comp] using
    (Functor.rightDerivedNatTrans_app
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
      (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
      F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
      (HomotopyCategory.Plus.quasiIso D) (𝟙 _) K)

private lemma derived_unit_comparison (adj : L ⊣ R)
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map (adj.derivedPlus.unit.app K) ≫
      R.rightDerivedFunctorPlusCompatibility.hom.app (L.mapDerivedCategoryPlus.obj K) =
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app K.obj := by
  let η : DerivedCategory.Plus.ι ⟶
      L.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙ R.rightDerivedFunctor :=
    Functor.whiskerRight adj.derivedPlus.unit DerivedCategory.Plus.ι ≫
      Functor.whiskerLeft L.mapDerivedCategoryPlus R.rightDerivedFunctorPlusCompatibility.hom
  let ε : DerivedCategory.Plus.ι ⟶
      L.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙ R.rightDerivedFunctor :=
    Functor.whiskerLeft DerivedCategory.Plus.ι
      adj.mapDerivedCategoryRightDerivedAdjunction.unit
  have he : η = ε := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)
    intro N
    dsimp only [η, ε, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app]
    apply (cancel_mono (R.rightDerivedFunctor.map
      (L.mapDerivedCategoryFactorsh.hom.app N.obj))).1
    have hn := R.rightDerivedFunctorPlusCompatibility.hom.naturality
      (L.mapDerivedCategoryPlusFactorsh.hom.app N)
    dsimp only [Functor.comp_map] at hn
    have hf : L.mapDerivedCategoryFactorsh.hom.app N.obj =
        DerivedCategory.Plus.ι.map (L.mapDerivedCategoryPlusFactorsh.hom.app N) :=
      (L.ι_map_mapDerivedCategoryPlusFactorsh_hom_app N).symm
    erw [hf]
    erw [Category.assoc, ← hn, ← Functor.map_comp_assoc,
      adj.derivedPlus_unit_app_fac, Functor.map_comp, Category.assoc, plus_comparison_unit]
    have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit N.obj
    change adj.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫ _ = _ at h
    erw [← hf, h]
    change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι C).map
      (adj.mapHomotopyCategoryPlus.unit.app N)) ≫ _ = _
    rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app]
    rfl
  exact NatTrans.congr_app he K

private lemma derived_counit_comparison (adj : L ⊣ R)
    (K : DerivedCategory.Plus D) :
    L.mapDerivedCategory.map (R.rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app K.obj =
    DerivedCategory.Plus.ι.map (adj.derivedPlus.counit.app K) := by
  apply (adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hn := adj.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (R.rightDerivedFunctorPlusCompatibility.hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  simp only [Functor.map_comp, ← Category.assoc, Functor.comp_obj, ObjectProperty.ι_obj]
  erw [← hn, Category.assoc,
    adj.mapDerivedCategoryRightDerivedAdjunction.right_triangle_components K.obj,
    Category.comp_id]
  erw [← derived_unit_comparison adj (R.rightDerivedFunctorPlus.obj K)]
  have hc := R.rightDerivedFunctorPlusCompatibility.hom.naturality
    (adj.derivedPlus.counit.app K)
  dsimp only [Functor.comp_map] at hc
  erw [Category.assoc, ← hc, ← Functor.map_comp_assoc]
  simp only [Adjunction.right_triangle_components]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end

private theorem square_fac
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (G : A ⥤ C) (L : A ⥤ B) (L' : C ⥤ D) (H : B ⥤ D)
    [G.Additive] [L.Additive] [L'.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L]
    [Limits.PreservesFiniteLimits L'] [Limits.PreservesFiniteColimits L']
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : G ⋙ L' ≅ L ⋙ H) (K : HomotopyCategory.Plus A) :
    ((Functor.mapDerivedCategoryPlusCompIso G L').symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso e ≪≫
      Functor.mapDerivedCategoryPlusCompIso L H).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        H.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        H.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
      L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  rw [← Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh G L' K]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]

section

variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C] [HasDerivedCategory C']
  [EnoughInjectives B] [EnoughInjectives B']
  {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteLimits G']
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

end

private theorem derived_mate_plus_comparison
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    [EnoughInjectives D] [EnoughInjectives D']
    [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {G' : D ⥤ D'}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (θ : G.mapDerivedCategoryPlus ⋙ L'.mapDerivedCategoryPlus ⟶
      L.mapDerivedCategoryPlus ⋙ G'.mapDerivedCategoryPlus)
    (Θ : G.mapDerivedCategory ⋙ L'.mapDerivedCategory ⟶
      L.mapDerivedCategory ⋙ G'.mapDerivedCategory)
    (hθ : ∀ M, DerivedCategory.Plus.ι.map (θ.app M) = Θ.app M.obj)
    (K : DerivedCategory.Plus D) :
    (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction (TwoSquare.mk _ _ _ _ Θ)).app
        K.obj =
    G.mapDerivedCategory.map (R.rightDerivedFunctorPlusCompatibility.inv.app K) ≫
      DerivedCategory.Plus.ι.map
        ((mateEquiv adj.derivedPlus adj'.derivedPlus
          (TwoSquare.mk _ _ _ _ θ)).app K) ≫
      R'.rightDerivedFunctorPlusCompatibility.hom.app (G'.mapDerivedCategoryPlus.obj K) := by
  apply (cancel_epi (G.mapDerivedCategory.map
    (R.rightDerivedFunctorPlusCompatibility.hom.app K))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (G.mapDerivedCategory.map (R.rightDerivedFunctorPlusCompatibility.hom.app K))
  have ht := Θ.naturality (R.rightDerivedFunctorPlusCompatibility.hom.app K)
  have hc := derived_counit_comparison adj K
  have hu := derived_unit_comparison adj'
    (G.mapDerivedCategoryPlus.obj (R.rightDerivedFunctorPlus.obj K))
  simp only [Functor.id_map, Functor.comp_map] at hn ht
  simp only [mate_app, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  simp only [← Functor.map_comp]
  erw [reassoc_of% ht, ← Functor.map_comp G'.mapDerivedCategory, hc]
  erw [← hθ, ← hu]
  have hb := R'.rightDerivedFunctorPlusCompatibility.hom.naturality
    (θ.app (R.rightDerivedFunctorPlus.obj K) ≫
      G'.mapDerivedCategoryPlus.map (adj.derivedPlus.counit.app K))
  dsimp only [Functor.comp_map] at hb
  simpa only [Functor.map_comp, Category.assoc, Functor.id_obj, Functor.comp_obj,
    ObjectProperty.ι_obj, inclusion_exact_map] using
    congrArg (fun a ↦ DerivedCategory.Plus.ι.map
      (adj'.derivedPlus.unit.app
        (G.mapDerivedCategoryPlus.obj (R.rightDerivedFunctorPlus.obj K))) ≫ a) hb.symm

namespace AlgebraicGeometry.Etale

private theorem exact_exchange_plus
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (exactDerivedBaseChangeMap A sq).app K.obj =
      (D((g)^*[A])).map (((f)_*[A]).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
        DerivedCategory.Plus.ι.map ((derivedBaseChangeMapPlus A sq).app K) ≫
        ((f')_*[A]).rightDerivedFunctorPlusCompatibility.hom.app
          ((D+((g')^*[A])).obj K) := by
  let θ := (Functor.mapDerivedCategoryPlusCompIso (g)^*[A] (f')^*[A]).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (squareUpperStarIso A sq) ≪≫
    Functor.mapDerivedCategoryPlusCompIso (f)^*[A] (g')^*[A]
  have hm : (mateEquiv (upperStarLowerStarAdjunction A f).derivedPlus
      (upperStarLowerStarAdjunction A f').derivedPlus
      (TwoSquare.mk _ _ _ _ θ.hom)) = derivedBaseChangeMapPlus A sq := by
    apply derivedBaseChangeMapPlus_ext A sq
    intro N
    exact Adjunction.derivedPlus_mateEquiv_app_fac
      (upperStarLowerStarAdjunction A f) (upperStarLowerStarAdjunction A f')
      (TwoSquare.mk _ _ _ _ (squareUpperStarIso A sq).hom)
      (TwoSquare.mk _ _ _ _ θ.hom)
      (square_fac _ _ _ _ (squareUpperStarIso A sq)) N
  have hθ (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
      DerivedCategory.Plus.ι.map (θ.hom.app M) =
        (exactDerivedSquareUpperStarIso A sq).hom.app M.obj := by
    have hi : DerivedCategory.Plus.ι.map
        ((Functor.mapDerivedCategoryPlusCompIso (g)^*[A] (f')^*[A]).inv.app M) =
        (Functor.mapDerivedCategoryCompIso (g)^*[A] (f')^*[A]).hom.app M.obj := by
      apply (cancel_mono
        ((Functor.mapDerivedCategoryCompIso (g)^*[A] (f')^*[A]).inv.app M.obj)).1
      erw [← Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
        ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
        Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, Iso.hom_inv_id_app]
      rfl
    simp only [θ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app, hi]
    rfl
  -- Transport the mate using the fixed direct-image comparison.
  exact derived_mate_plus_comparison (upperStarLowerStarAdjunction A f)
    (upperStarLowerStarAdjunction A f') θ.hom
    (exactDerivedSquareUpperStarIso A sq).hom hθ K |>.trans (by rw [hm])

end AlgebraicGeometry.Etale
