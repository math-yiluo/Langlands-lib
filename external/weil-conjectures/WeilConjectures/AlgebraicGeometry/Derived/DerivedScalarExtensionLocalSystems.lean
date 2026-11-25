/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalIsomorphismSourceEvaluation
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import Mathlib.CategoryTheory.Adjunction.Opposites
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.CategoryTheory.Derived.DerivedMorphismPresheaf
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Localized derived extension of coefficients and comparison

Source: Stacks Project, Cohomology on Sites, Tags 06YY, 0D6D, 07A4 and 0G7E.
(blueprint: lem-weil-pbc-derived-scalar-extension-local-systems)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
open scoped CategoryTheory.TwoSquare

open scoped CategoryTheory.TwoSquare
private theorem inverse_mate_paste
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {L : A ⥤ B} {U : B ⥤ A} {M : C ⥤ D} {V : D ⥤ C}
    {N : E ⥤ F} {W : F ⥤ E}
    (a : L ⊣ U) (b : M ⊣ V) (c : N ⊣ W)
    {G : A ⥤ C} {H : B ⥤ D} {I : C ⥤ E} {J : D ⥤ F}
    (x : TwoSquare U H G V) (y : TwoSquare V J I W) :
    (mateEquiv a c).symm (x ≫ᵥ y) =
      ((mateEquiv a b).symm x) ≫ₕ ((mateEquiv b c).symm y) := by
  apply (mateEquiv a c).injective
  rw [Equiv.apply_symm_apply, mateEquiv_vcomp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

private theorem inverse_mate_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {M : C ⥤ D} {V : D ⥤ C}
    (a : L ⊣ U) (b : M ⊣ V)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (x : TwoSquare U H G V) (e : G ≅ G') (f : H ≅ H') :
    ((mateEquiv a b).symm
      (TwoSquare.mk U H' G' V
        (Functor.whiskerLeft U e.inv ≫ x ≫ Functor.whiskerRight f.hom V))) =
      Functor.whiskerRight e.inv M ≫ ((mateEquiv a b).symm x) ≫
        Functor.whiskerLeft L f.hom := by
  ext z
  simp only [mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Functor.map_comp,
    Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp, Category.comp_id, M.map_comp, Category.assoc]
  have he := e.inv.naturality (a.unit.app z)
  dsimp only [Functor.comp_obj, Functor.id_obj] at he
  rw [← M.map_comp_assoc, he, M.map_comp]
  simp only [Category.assoc]
  have hf := b.counit.naturality (f.hom.app (L.obj z))
  dsimp only [Functor.comp_map, Functor.id_map] at hf
  erw [Category.comp_id]
  erw [Category.id_comp]
  rw [hf]

private theorem inverse_mate_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {L : A ⥤ A'} {U : A' ⥤ A} {l : B ⥤ B'} {u : B' ⥤ B}
    {M : C ⥤ C'} {V : C' ⥤ C} {m : D ⥤ D'} {v : D' ⥤ D}
    (a : L ⊣ U) (al : l ⊣ u) (am : M ⊣ V) (ad : m ⊣ v)
    {r : A ⥤ B} {r' : A' ⥤ B'} {H : A ⥤ C} {H' : A' ⥤ C'}
    {K : B ⥤ D} {K' : B' ⥤ D'} {s : C ⥤ D} {s' : C' ⥤ D'}
    (t : TwoSquare U r' r u) (k : TwoSquare u K' K v)
    (c : TwoSquare U H' H V) (q : TwoSquare V s' s v)
    (b : r ⋙ K ≅ H ⋙ s) (b' : r' ⋙ K' ≅ H' ⋙ s')
    (h : t ≫ᵥ k = TwoSquare.mk U (r' ⋙ K') (r ⋙ K) v
      (Functor.whiskerLeft U b.hom ≫ (c ≫ᵥ q) ≫
        Functor.whiskerRight b'.inv v)) (x : A) :
    m.map (b.hom.app x) ≫
        ((mateEquiv am ad).symm q).app (H.obj x) ≫
        s'.map (((mateEquiv a am).symm c).app x) =
      ((mateEquiv al ad).symm k).app (r.obj x) ≫
        K'.map (((mateEquiv a al).symm t).app x) ≫ b'.hom.app (L.obj x) := by
  have ht := inverse_mate_paste a al ad t k
  have hq := inverse_mate_paste a am ad c q
  rw [h] at ht
  have hn := inverse_mate_transport a ad (c ≫ᵥ q) b.symm b'.symm
  have hp := congrArg (fun w ↦ w.app x) ht
  dsimp only [Iso.symm_hom, Iso.symm_inv] at hn
  rw [NatTrans.congr_app hn] at hp
  rw [hq] at hp
  simp only [TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.symm_hom, Iso.symm_inv, Category.comp_id,
    Category.id_comp, Category.assoc] at hp
  have hh := congrArg (fun f ↦ f ≫ b'.hom.app (L.obj x)) hp
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh

namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {B B' : Type (u + 1)}
  [CommRing B] [CommRing B'] (φ : B →+* B')
end CategoryTheory
namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {B B' : Type (u + 1)}
  [CommRing B] [CommRing B'] (φ : B →+* B')

private noncomputable def mapScalarsSheafIso {U V : C} (f : V ⟶ U) :
    Sheaf.restrictScalars (J.over U) φ ⋙ J.overMapPullback (ModuleCat.{u + 1} B) f ≅
      J.overMapPullback (ModuleCat.{u + 1} B') f ⋙
        Sheaf.restrictScalars (J.over V) φ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private noncomputable def mapScalarsIso {U V : C} (f : V ⟶ U) :
    Sheaf.derivedRestrictScalars (J.over U) φ ⋙ derivedSliceMap J B f ≅
      derivedSliceMap J B' f ⋙ Sheaf.derivedRestrictScalars (J.over V) φ :=
  Functor.mapDerivedCategorySquareIso (mapScalarsSheafIso J φ f)

private theorem restriction_scalars_paste {U V : C} (f : V ⟶ U)
    (A : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B'))) :
    (sliceRestrictScalarsIso J B φ V).inv.app A ≫
        (Sheaf.derivedRestrictScalars (J.over V) φ).map
          ((derivedSliceMapIso J B' f).inv.app A) =
      (derivedSliceMapIso J B f).inv.app
          ((Sheaf.derivedRestrictScalars J φ).obj A) ≫
        (derivedSliceMap J B f).map ((sliceRestrictScalarsIso J B φ U).inv.app A) ≫
        (mapScalarsIso J φ f).hom.app ((derivedSliceRestriction J B' U).obj A) := by
  have h := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (sliceRestrictScalarsSheafIso J B φ U).symm
    (mapScalarsSheafIso J φ f)
    (sliceRestrictScalarsSheafIso J B φ V).symm
    (sliceRestrictionMapIso J B f).symm
    (sliceRestrictionMapIso J B' f).symm
    (fun M ↦ by ext W x; rfl) A
  simpa only [sliceRestrictScalarsIso, mapScalarsIso, derivedSliceMapIso,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc] using h
end CategoryTheory

namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {B B' : Type (u + 1)}
  [CommRing B] [CommRing B'] (φ : B →+* B')

end CategoryTheory

namespace CategoryTheory
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  (J : GrothendieckTopology C) (F : C ⥤ D) (K : GrothendieckTopology D)
  [F.IsContinuous J K]
  {R S : Type (u + 1)} [CommRing R] [CommRing S]

omit [EssentiallySmall.{u + 1} C] in
private theorem normalMate_eq_conjugate (q : R →+* S) :
    normalizationPullbackMate J F K q =
      (conjugateEquiv
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
          (ModuleCat.{u + 1} S) J K).comp (Sheaf.restrictCoextendScalarsAdj K q))
        ((Sheaf.restrictCoextendScalarsAdj J q).comp
          (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
            (ModuleCat.{u + 1} R) J K))).symm (𝟙 _) := by
  let adjU := ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} q
  have : (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} q).IsRightAdjoint :=
    adjU.isRightAdjoint
  let adjJ := sheafComposeAdjunction J adjU
  let adjK := sheafComposeAdjunction K adjU
  let adjS := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    (ModuleCat.{u + 1} S) J K
  let adjR := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    (ModuleCat.{u + 1} R) J K
  let γ := TwoSquare.mk
    (sheafCompose K (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} q))
    (F.sheafPushforwardContinuous (ModuleCat.{u + 1} R) J K)
    (F.sheafPushforwardContinuous (ModuleCat.{u + 1} S) J K)
    (sheafCompose J (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} q)) (𝟙 _)
  have hγ : (mateEquiv adjK adjJ).symm γ = TwoSquare.mk _ _ _ _ (𝟙 _) := by
    ext X : 2
    apply Sheaf.hom_ext
    simp only [Functor.comp_obj, mateEquiv_symm_apply, NatTrans.comp_app, Functor.id_obj,
      Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.comp_map,
      Functor.associator_inv_app, Functor.associator_hom_app, CategoryTheory.Functor.map_id,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.comp_id,
      Category.id_comp, ObjectProperty.FullSubcategory.comp_hom, sheafCompose_map_hom,
      NatTrans.id_app, ObjectProperty.FullSubcategory.id_hom]
    apply NatTrans.ext
    funext Y
    exact adjU.left_triangle_components (X.obj.obj (F.op.obj Y))
  unfold normalizationPullbackMate
  rw [← hγ]
  rw [iterated_mateEquiv_conjugateEquiv_symm adjS adjR adjJ adjK]
  rfl
end CategoryTheory
namespace AlgebraicGeometry.ProEtale
variable {R S : Type (u + 1)} [CommRing R] [CommRing S]
set_option backward.isDefEq.respectTransparency false in
private theorem normalPullback_proet (q : R →+* S) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ f).IsContinuous
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
        Scheme.ProEt.isContinuous_overPullback f
    (normalizationPullbackIso (Scheme.ProEt.topology Y)
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ f)
      (Scheme.ProEt.topology X) q).hom = (upperStarRestrictScalarsIso q f).hom := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ f).IsContinuous
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
        Scheme.ProEt.isContinuous_overPullback f
  simp only [normalizationPullbackIso, asIso_hom, CategoryTheory.normalMate_eq_conjugate]
  rfl
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
variable {R S : Type (u + 1)} [CommRing R] [CommRing S]
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (U : X.ProEt)
set_option backward.isDefEq.respectTransparency false in
private theorem proet_coefficient_mate_eq (q : R →+* S)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom)
      (ProEt.topology U.left) q).hom.app M =
      ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) U.hom).homEquiv _ _).symm
        ((sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) U.hom).unit.app M)) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  simp only [normalizationPullbackIso, asIso_hom, normalizationPullbackMate,
    mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Adjunction.homEquiv_counit]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem proet_localization_coefficient_mate (q : R →+* S)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom)
      (ProEt.topology U.left) q).hom.app M ≫
        (sheafCompose (ProEt.topology U.left)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((ProEtale.upperStarIsoLocalizationRestriction
            (ModuleCat.{u + 1} S) U.hom U.prop).hom.app M) =
      (ProEtale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} R) U.hom U.prop).hom.app
          ((sheafCompose (ProEt.topology X)
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  let aR := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) U.hom
  let aS := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) U.hom
  let bR := ProEtale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} R) U.hom U.prop
  let bS := ProEtale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} S) U.hom U.prop
  apply (aR.homEquiv _ _).injective
  rw [aR.homEquiv_naturality_right, proet_coefficient_mate_eq,
    Equiv.apply_symm_apply]
  change _ = aR.homEquiv _ _ ((aR.leftAdjointUniq bR).hom.app _)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have hs := Adjunction.homEquiv_leftAdjointUniq_hom_app aS bS M
  rw [Adjunction.homEquiv_unit] at hs
  change
    (sheafCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map (aS.unit.app M) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} R) U.hom).map
        ((sheafCompose (ProEt.topology U.left)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((aS.leftAdjointUniq bS).hom.app M)) = _
  change (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
      (aS.unit.app M) ≫
    (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
      ((ProEtale.lowerStar (ModuleCat.{u + 1} S) U.hom).map
        ((aS.leftAdjointUniq bS).hom.app M)) = _
  rw [← CategoryTheory.Functor.map_comp, hs]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]

private noncomputable def proetSliceEquivalenceCoefficients (U : X.ProEt) (q : R →+* S) :
    Sheaf.restrictScalars ((ProEt.topology X).over U) q ⋙
        (proetSliceEquivalence X R U).functor ≅
      (proetSliceEquivalence X S U).functor ⋙
        Sheaf.restrictScalars (ProEt.topology U.left) q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

set_option backward.isDefEq.respectTransparency false in
private theorem proetSliceCoefficients_pasting (U : X.ProEt) (q : R →+* S)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom)
      (ProEt.topology U.left) q).hom.app M ≫
      (Sheaf.restrictScalars (ProEt.topology U.left) q).map
        ((proetSliceRestrictionIso X S U).inv.app M) =
    (proetSliceRestrictionIso X R U).inv.app
      ((Sheaf.restrictScalars (ProEt.topology X) q).obj M) ≫
      (proetSliceEquivalence X R U).functor.map
        ((sliceRestrictScalarsSheafIso (ProEt.topology X) R q U).inv.app M) ≫
      (proetSliceEquivalenceCoefficients X U q).hom.app
        (((ProEt.topology X).overPullback (ModuleCat.{u + 1} S) U).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  have h := proet_localization_coefficient_mate X U q M
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  have hh := congrArg (fun k ↦ k.hom.app V) h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun k ↦ k x) hh

private noncomputable def proetExactCoefficients (U : X.ProEt) (q : R →+* S) :=
  Functor.mapDerivedCategorySquareIso (ProEtale.upperStarRestrictScalarsIso q U.hom)

private noncomputable def proetDerivedSliceEquivalenceCoefficients (U : X.ProEt) (q : R →+* S) :
    Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) q ⋙
        (proetSliceEquivalence X R U).functor.mapDerivedCategory ≅
      (proetSliceEquivalence X S U).functor.mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (ProEt.topology U.left) q :=
  Functor.mapDerivedCategorySquareIso (proetSliceEquivalenceCoefficients X U q)

set_option backward.isDefEq.respectTransparency false in
private theorem proetDerivedSliceCoefficients_pasting (U : X.ProEt) (q : R →+* S)
    (M : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S))) :
    (proetExactCoefficients X U q).hom.app M ≫
      (normalizationRestrict (ProEt.topology U.left) q).map
        ((proetDerivedSliceRestrictionIso X S U).inv.app M) =
    (proetDerivedSliceRestrictionIso X R U).inv.app
      ((normalizationRestrict (ProEt.topology X) q).obj M) ≫
      (proetSliceEquivalence X R U).functor.mapDerivedCategory.map
        ((sliceRestrictScalarsIso (ProEt.topology X) R q U).inv.app M) ≫
      (proetDerivedSliceEquivalenceCoefficients X U q).hom.app
        ((derivedSliceRestriction (ProEt.topology X) S U).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  let : (Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback
      @AlgebraicGeometry.WeaklyEtale ⊤ U.hom) (ModuleCat.{u + 1} S)
      (ProEt.topology X) (ProEt.topology U.left)).Additive := by
    change (ProEtale.upperStar (ModuleCat.{u + 1} S) U.hom).Additive
    infer_instance
  let : (Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback
      @AlgebraicGeometry.WeaklyEtale ⊤ U.hom) (ModuleCat.{u + 1} R)
      (ProEt.topology X) (ProEt.topology U.left)).Additive := by
    change (ProEtale.upperStar (ModuleCat.{u + 1} R) U.hom).Additive
    infer_instance
  let : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom)
      (ModuleCat.{u + 1} R) (ProEt.topology X) (ProEt.topology U.left)) := by
    change PreservesFiniteLimits (ProEtale.upperStar (ModuleCat.{u + 1} R) U.hom)
    infer_instance
  let : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom)
      (ModuleCat.{u + 1} R) (ProEt.topology X) (ProEt.topology U.left)) := by
    change PreservesFiniteColimits (ProEtale.upperStar (ModuleCat.{u + 1} R) U.hom)
    infer_instance
  let : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom)
      (ModuleCat.{u + 1} S) (ProEt.topology X) (ProEt.topology U.left)) := by
    change PreservesFiniteLimits (ProEtale.upperStar (ModuleCat.{u + 1} S) U.hom)
    infer_instance
  let : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom)
      (ModuleCat.{u + 1} S) (ProEt.topology X) (ProEt.topology U.left)) := by
    change PreservesFiniteColimits (ProEtale.upperStar (ModuleCat.{u + 1} S) U.hom)
    infer_instance
  have he : normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom) (ProEt.topology U.left) q =
      ProEtale.upperStarRestrictScalarsIso q U.hom := by
    apply Iso.ext
    exact ProEtale.normalPullback_proet q U.hom
  have h := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (sliceRestrictScalarsSheafIso (ProEt.topology X) R q U).symm
    (proetSliceEquivalenceCoefficients X U q)
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom)
      (ProEt.topology U.left) q)
    (proetSliceRestrictionIso X R U).symm
    (proetSliceRestrictionIso X S U).symm
    (proetSliceCoefficients_pasting X U q) M
  rw [he] at h
  simp only [proetExactCoefficients, proetDerivedSliceRestrictionIso,
    proetDerivedSliceEquivalenceCoefficients, sliceRestrictScalarsIso,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc] at h ⊢
  convert! h using 1

end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale
variable {R S : Type (u + 1)} [CommRing R] [CommRing S]
private theorem normalPullback_etale (q : R →+* S) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := isContinuous_overPullback f
    (normalizationPullbackIso Y.smallEtaleTopology
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      X.smallEtaleTopology q).hom = (upperStarRestrictScalarsIsoSheaf q f).hom := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := isContinuous_overPullback f
  let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) f
  let b := upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f
  let c := Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology q
  let d := Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology q
  have h : (upperStarRestrictScalarsIsoSheaf q f).hom =
      (conjugateEquiv (a.comp c) (d.comp b)).symm (𝟙 _) := rfl
  rw [h]
  change normalizationPullbackMate Y.smallEtaleTopology
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
      X.smallEtaleTopology q = _
  exact CategoryTheory.normalMate_eq_conjugate Y.smallEtaleTopology
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
    X.smallEtaleTopology q
end AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
variable {R S : Type (u + 1)} [CommRing R] [CommRing S]
private theorem exact_scalar_mate_etale (q : R →+* S) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso ((mateEquiv
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology q))).symm
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso
          (upperStarRestrictScalarsIsoSheaf q f)).hom)) := by
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q)
  let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology q)
  let x := TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso q f).hom
  let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) f
  let e' := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} S) f
  have hx : IsIso ((mateEquiv a b).symm x) := (ProEtale.scalarPullbackReverse_isIso q f).2
  have h := inverse_mate_transport a b x e e'
  have ht : IsIso (Functor.whiskerRight e.inv _ ≫
      ((mateEquiv a b).symm x) ≫ Functor.whiskerLeft _ e'.hom) := inferInstance
  rw [← h] at ht
  have heq : TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf q f)).hom =
      TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q)
          e.inv ≫ x ≫
          Functor.whiskerRight e'.hom
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology q)) := by
    ext M
    dsimp only [x, e, e', scalarRestrictionPullbackIso, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  rw [← heq] at ht
  exact ht
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
variable (U : X.Etale)
set_option backward.isDefEq.respectTransparency false in
private theorem etale_coefficient_mate_eq (q : R →+* S)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      X.smallEtaleTopology U.left.smallEtaleTopology := Etale.isContinuous_overPullback U.hom
    (normalizationPullbackIso X.smallEtaleTopology
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      U.left.smallEtaleTopology q).hom.app M =
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) U.hom).homEquiv _ _).symm
        ((sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) U.hom).unit.app M)) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      X.smallEtaleTopology U.left.smallEtaleTopology := Etale.isContinuous_overPullback U.hom
  simp only [normalizationPullbackIso, asIso_hom, normalizationPullbackMate,
    mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Adjunction.homEquiv_counit]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem etale_localization_coefficient_mate (q : R →+* S)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      X.smallEtaleTopology U.left.smallEtaleTopology := Etale.isContinuous_overPullback U.hom
    (normalizationPullbackIso X.smallEtaleTopology
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      U.left.smallEtaleTopology q).hom.app M ≫
        (sheafCompose U.left.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((Etale.upperStarIsoLocalizationRestriction
            (ModuleCat.{u + 1} S) U.hom U.prop).hom.app M) =
      (Etale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} R) U.hom U.prop).hom.app
          ((sheafCompose X.smallEtaleTopology
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      X.smallEtaleTopology U.left.smallEtaleTopology := Etale.isContinuous_overPullback U.hom
  let aR := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) U.hom
  let aS := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) U.hom
  let bR := Etale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} R) U.hom U.prop
  let bS := Etale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} S) U.hom U.prop
  apply (aR.homEquiv _ _).injective
  rw [aR.homEquiv_naturality_right, etale_coefficient_mate_eq,
    Equiv.apply_symm_apply]
  change _ = aR.homEquiv _ _ ((aR.leftAdjointUniq bR).hom.app _)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have hs := Adjunction.homEquiv_leftAdjointUniq_hom_app aS bS M
  rw [Adjunction.homEquiv_unit] at hs
  change
    (sheafCompose X.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map (aS.unit.app M) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} R) U.hom).map
        ((sheafCompose U.left.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((aS.leftAdjointUniq bS).hom.app M)) = _
  change (sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
      (aS.unit.app M) ≫
    (sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
      ((Etale.lowerStar (ModuleCat.{u + 1} S) U.hom).map
        ((aS.leftAdjointUniq bS).hom.app M)) = _
  rw [← CategoryTheory.Functor.map_comp, hs]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]

private noncomputable def etaleSliceEquivalenceCoefficients (U : X.Etale) (q : R →+* S) :
    Sheaf.restrictScalars (X.smallEtaleTopology.over U) q ⋙
        (Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor ≅
      (Etale.overSheafEquiv U (ModuleCat.{u + 1} S)).functor ⋙
        Sheaf.restrictScalars U.left.smallEtaleTopology q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

set_option backward.isDefEq.respectTransparency false in
private theorem etaleSliceCoefficients_pasting (U : X.Etale) (q : R →+* S)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      X.smallEtaleTopology U.left.smallEtaleTopology := Etale.isContinuous_overPullback U.hom
    (normalizationPullbackIso X.smallEtaleTopology
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      U.left.smallEtaleTopology q).hom.app M ≫
      (Sheaf.restrictScalars U.left.smallEtaleTopology q).map
        ((etaleSliceRestrictionIso X S U).inv.app M) =
    (etaleSliceRestrictionIso X R U).inv.app
      ((Sheaf.restrictScalars X.smallEtaleTopology q).obj M) ≫
      (Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor.map
        ((sliceRestrictScalarsSheafIso X.smallEtaleTopology R q U).inv.app M) ≫
      (etaleSliceEquivalenceCoefficients X U q).hom.app
        ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} S) U).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      X.smallEtaleTopology U.left.smallEtaleTopology := Etale.isContinuous_overPullback U.hom
  have h := etale_localization_coefficient_mate X U q M
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  have hh := congrArg (fun k ↦ k.hom.app V) h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun k ↦ k x) hh

end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
private noncomputable def etaleExactCoefficients (U : X.Etale) (q : R →+* S) :
    Sheaf.derivedRestrictScalars X.smallEtaleTopology q ⋙
        (Etale.upperStar (ModuleCat.{u + 1} R) U.hom).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} S) U.hom).mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars U.left.smallEtaleTopology q :=
  Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIsoSheaf q U.hom)
private noncomputable def etaleDerivedSliceEquivalenceCoefficients (U : X.Etale) (q : R →+* S) :
    Sheaf.derivedRestrictScalars (X.smallEtaleTopology.over U) q ⋙
        (Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor.mapDerivedCategory ≅
      (Etale.overSheafEquiv U (ModuleCat.{u + 1} S)).functor.mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars U.left.smallEtaleTopology q :=
  Functor.mapDerivedCategorySquareIso (etaleSliceEquivalenceCoefficients X U q)

set_option backward.isDefEq.respectTransparency false in
private theorem etaleDerivedSliceCoefficients_pasting (U : X.Etale) (q : R →+* S)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))) :
    (etaleExactCoefficients X U q).hom.app M ≫
      (normalizationRestrict U.left.smallEtaleTopology q).map
        ((etaleDerivedSliceRestrictionIso X S U).inv.app M) =
    (etaleDerivedSliceRestrictionIso X R U).inv.app
      ((normalizationRestrict X.smallEtaleTopology q).obj M) ≫
      (Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor.mapDerivedCategory.map
        ((sliceRestrictScalarsIso X.smallEtaleTopology R q U).inv.app M) ≫
      (etaleDerivedSliceEquivalenceCoefficients X U q).hom.app
        ((derivedSliceRestriction X.smallEtaleTopology S U).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      X.smallEtaleTopology U.left.smallEtaleTopology := Etale.isContinuous_overPullback U.hom
  let : (Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback
      @AlgebraicGeometry.Etale ⊤ U.hom) (ModuleCat.{u + 1} S)
      X.smallEtaleTopology U.left.smallEtaleTopology).Additive := by
    change (Etale.upperStar (ModuleCat.{u + 1} S) U.hom).Additive
    infer_instance
  let : (Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback
      @AlgebraicGeometry.Etale ⊤ U.hom) (ModuleCat.{u + 1} R)
      X.smallEtaleTopology U.left.smallEtaleTopology).Additive := by
    change (Etale.upperStar (ModuleCat.{u + 1} R) U.hom).Additive
    infer_instance
  let : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} R) X.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{u + 1} R) U.hom)
    infer_instance
  let : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} R) X.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{u + 1} R) U.hom)
    infer_instance
  let : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} S) X.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteLimits (Etale.upperStar (ModuleCat.{u + 1} S) U.hom)
    infer_instance
  let : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      (ModuleCat.{u + 1} S) X.smallEtaleTopology U.left.smallEtaleTopology) := by
    change PreservesFiniteColimits (Etale.upperStar (ModuleCat.{u + 1} S) U.hom)
    infer_instance
  have he : normalizationPullbackIso X.smallEtaleTopology
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      U.left.smallEtaleTopology q = Etale.upperStarRestrictScalarsIsoSheaf q U.hom := by
    apply Iso.ext
    exact Etale.normalPullback_etale q U.hom
  have h := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (sliceRestrictScalarsSheafIso X.smallEtaleTopology R q U).symm
    (etaleSliceEquivalenceCoefficients X U q)
    (normalizationPullbackIso X.smallEtaleTopology
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom)
      U.left.smallEtaleTopology q)
    (etaleSliceRestrictionIso X R U).symm
    (etaleSliceRestrictionIso X S U).symm
    (etaleSliceCoefficients_pasting X U q) M
  rw [he] at h
  simp only [etaleExactCoefficients, etaleDerivedSliceRestrictionIso,
    etaleDerivedSliceEquivalenceCoefficients, etaleDerivedSliceEquivalence_functor,
    sliceRestrictScalarsIso,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc] at h ⊢
  convert! h using 1

end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
set_option backward.isDefEq.respectTransparency false in
private theorem comparison_coefficient_mate_eq (q : R →+* S)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)) :
    (normalizationPullbackIso X.smallEtaleTopology (toProEt X) (ProEt.topology X) q).hom.app M =
      comparisonRestrictScalarsMap X R q M := by
  simp only [normalizationPullbackIso, asIso_hom, normalizationPullbackMate,
    mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, comparisonRestrictScalarsMap,
    Adjunction.homEquiv_counit]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_coefficient_derived_eq (q : R →+* S) :
    localIsomorphismComparisonCoefficients (X := X) q =
      comparisonRestrictScalarsIso X R q := by
  have h : normalizationPullbackIso X.smallEtaleTopology (toProEt X)
      (ProEt.topology X) q = comparisonRestrictScalarsSheafIso X R q := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    exact comparison_coefficient_mate_eq X q M
  unfold localIsomorphismComparisonCoefficients comparisonRestrictScalarsIso
  rw [h]

end AlgebraicGeometry.Scheme

private theorem derived_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [Abelian A'] [Abelian B'] [Abelian C'] [Abelian D']
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory A'] [HasDerivedCategory B']
    [HasDerivedCategory C'] [HasDerivedCategory D']
    (U : A' ⥤ A) (V : B' ⥤ B) (W : C' ⥤ C) (Z : D' ⥤ D)
    (r : A ⥤ B) (r' : A' ⥤ B') (s : C ⥤ D) (s' : C' ⥤ D')
    (H : A ⥤ C) (H' : A' ⥤ C') (K : B ⥤ D) (K' : B' ⥤ D')
    [U.Additive] [V.Additive] [W.Additive] [Z.Additive]
    [r.Additive] [r'.Additive] [s.Additive] [s'.Additive]
    [H.Additive] [H'.Additive] [K.Additive] [K'.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    [PreservesFiniteLimits Z] [PreservesFiniteColimits Z]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits r'] [PreservesFiniteColimits r']
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    [PreservesFiniteLimits s'] [PreservesFiniteColimits s']
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
    (t : U ⋙ r ≅ r' ⋙ V) (k : V ⋙ K ≅ K' ⋙ Z)
    (c : U ⋙ H ≅ H' ⋙ W) (q : W ⋙ s ≅ s' ⋙ Z)
    (b : r ⋙ K ≅ H ⋙ s) (b' : r' ⋙ K' ≅ H' ⋙ s')
    (h : ∀ x, K.map (t.hom.app x) ≫ k.hom.app (r'.obj x) ≫ Z.map (b'.hom.app x) =
      b.hom.app (U.obj x) ≫ s.map (c.hom.app x) ≫ q.hom.app (H'.obj x))
    (x : DerivedCategory A') :
    K.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso t).hom.app x) ≫
        (Functor.mapDerivedCategorySquareIso k).hom.app (r'.mapDerivedCategory.obj x) ≫
        Z.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso b').hom.app x) =
      (Functor.mapDerivedCategorySquareIso b).hom.app (U.mapDerivedCategory.obj x) ≫
        s.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso c).hom.app x) ≫
        (Functor.mapDerivedCategorySquareIso q).hom.app (H'.mapDerivedCategory.obj x) := by
  let a : U ⋙ (r ⋙ K) ≅ (r' ⋙ K') ⋙ Z :=
    Functor.isoWhiskerRight t K ≪≫ Functor.isoWhiskerLeft r' k
  have h₁ := Functor.mapDerivedCategorySquareIso_hom_app_comp t k a
    (Iso.refl (r ⋙ K)) (Iso.refl (r' ⋙ K')) (fun y ↦ by simp [a]) x
  have h₂ := Functor.mapDerivedCategorySquareIso_hom_app_comp c q a b b'
    (fun y ↦ by simpa [a] using h y) x
  simp only [Functor.mapDerivedCategoryTriangleIso, Functor.mapDerivedCategoryNatIso_refl,
    Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, NatTrans.comp_app,
    NatTrans.id_app, Category.comp_id, CategoryTheory.Functor.map_comp,
    Category.assoc, CategoryTheory.Functor.map_id, Category.id_comp] at h₁ h₂
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso r K).inv.app
    (U.mapDerivedCategory.obj x))]
  rw [← cancel_mono (Z.mapDerivedCategory.map
    ((Functor.mapDerivedCategoryCompIso H' s').hom.app x))]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% h₁, ← reassoc_of% h₂]
  simp only [← Z.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [Iso.inv_hom_id_app_assoc]

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
private noncomputable def comparisonSliceCoefficients (V : X.Etale) (q : R →+* S) :=
  normalizationPullbackIso (X.smallEtaleTopology.over V) (Over.post (toProEt X))
    ((ProEt.topology X).over ((toProEt X).obj V)) q

set_option backward.isDefEq.respectTransparency false in
private theorem comparisonSliceCoefficients_eq (V : X.Etale) (q : R →+* S)
    (M : Sheaf (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} S)) :
    (comparisonSliceCoefficients X V q).hom.app M =
      ((comparisonSliceAdjunction X R V).homEquiv _ _).symm
        ((Sheaf.restrictScalars (X.smallEtaleTopology.over V) q).map
          ((comparisonSliceAdjunction X S V).unit.app M)) := by
  simp only [comparisonSliceCoefficients, normalizationPullbackIso, asIso_hom,
    normalizationPullbackMate, mateEquiv_symm_apply, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Adjunction.homEquiv_counit]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_coefficients_cube (V : X.Etale) (q : R →+* S)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)) :
    (comparisonSliceCoefficients X V q).hom.app (M.over V) ≫
      (Sheaf.restrictScalars ((ProEt.topology X).over ((toProEt X).obj V)) q).map
        ((comparisonSliceBaseIso X S V).hom.app M) =
    (comparisonSliceBaseIso X R V).hom.app
      ((Sheaf.restrictScalars X.smallEtaleTopology q).obj M) ≫
      ((ProEt.topology X).overPullback (ModuleCat.{u + 1} R)
        ((toProEt X).obj V)).map
        ((comparisonRestrictScalarsSheafIso X R q).hom.app M) := by
  have hS := ((comparisonSliceAdjunction X S V).homEquiv (M.over V)
    (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X).obj M).over
      ((toProEt X).obj V))).apply_symm_apply
    ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} S) V).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} S) X).unit.app M))
  have hR := ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X).homEquiv
    ((Sheaf.restrictScalars X.smallEtaleTopology q).obj M)
    ((Sheaf.restrictScalars (ProEt.topology X) q).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X).obj M))).apply_symm_apply
    ((Sheaf.restrictScalars X.smallEtaleTopology q).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} S) X).unit.app M))
  rw [Adjunction.homEquiv_unit] at hS hR
  apply ((comparisonSliceAdjunction X R V).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, comparisonSliceCoefficients_eq,
    Equiv.apply_symm_apply]
  simp only [comparisonSliceBaseIso, NatIso.ofComponents_hom_app, asIso_hom]
  rw [Adjunction.homEquiv_naturality_right]
  erw [comparisonSliceBaseMap, Equiv.apply_symm_apply]
  change
    (Sheaf.restrictScalars (X.smallEtaleTopology.over V) q).map
      ((comparisonSliceAdjunction X S V).unit.app (M.over V)) ≫
      (Sheaf.restrictScalars (X.smallEtaleTopology.over V) q).map
        (((Over.post (toProEt X)).sheafPushforwardContinuous (ModuleCat.{u + 1} S)
          (X.smallEtaleTopology.over V)
          ((ProEt.topology X).over ((toProEt X).obj V))).map
          (comparisonSliceBaseMap X S V M)) =
    (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) V).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X).unit.app
        ((Sheaf.restrictScalars X.smallEtaleTopology q).obj M)) ≫
      (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) V).map
        ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} R) X).map
          (comparisonRestrictScalarsMap X R q M))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  change _ = (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) V).map
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X).unit.app
      ((Sheaf.restrictScalars X.smallEtaleTopology q).obj M) ≫
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} R) X).map
        (comparisonRestrictScalarsMap X R q M))
  rw [show (comparisonSliceAdjunction X S V).unit.app (M.over V) ≫
      ((Over.post (toProEt X)).sheafPushforwardContinuous (ModuleCat.{u + 1} S)
        (X.smallEtaleTopology.over V)
        ((ProEt.topology X).over ((toProEt X).obj V))).map
        (comparisonSliceBaseMap X S V M) = _ from hS]
  rw [show (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X).unit.app
      ((Sheaf.restrictScalars X.smallEtaleTopology q).obj M) ≫
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} R) X).map
        (comparisonRestrictScalarsMap X R q M) = _ from hR]
  rfl
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
private noncomputable def comparisonDerivedSliceCoefficients (V : X.Etale) (q : R →+* S) :=
  Functor.mapDerivedCategorySquareIso (comparisonSliceCoefficients X V q)

private theorem comparison_derived_coefficients_cube (V : X.Etale) (q : R →+* S)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))) :
    (comparisonSliceUpperStar X R V).mapDerivedCategory.map
        ((sliceRestrictScalarsIso X.smallEtaleTopology R q V).inv.app M) ≫
      (comparisonDerivedSliceCoefficients X V q).hom.app
        ((derivedSliceRestriction X.smallEtaleTopology S V).obj M) ≫
      (Sheaf.derivedRestrictScalars ((ProEt.topology X).over ((toProEt X).obj V)) q).map
        ((derivedComparisonSliceIso X S V).hom.app M) =
    (derivedComparisonSliceIso X R V).hom.app
      ((Sheaf.derivedRestrictScalars X.smallEtaleTopology q).obj M) ≫
      (derivedSliceRestriction (ProEt.topology X) R ((toProEt X).obj V)).map
        ((comparisonRestrictScalarsIso X R q).hom.app M) ≫
      (sliceRestrictScalarsIso (ProEt.topology X) R q ((toProEt X).obj V)).inv.app
        ((derivedComparison X S).obj M) := by
  have h := derived_cube _ _ _ _ _ _ _ _ _ _ _ _
    (sliceRestrictScalarsSheafIso X.smallEtaleTopology R q V).symm
    (comparisonSliceCoefficients X V q) (comparisonRestrictScalarsSheafIso X R q)
    (sliceRestrictScalarsSheafIso (ProEt.topology X) R q ((toProEt X).obj V)).symm
    (comparisonSliceBaseIso X R V) (comparisonSliceBaseIso X S V)
    (fun N ↦ by
      dsimp only [sliceRestrictScalarsSheafIso, Iso.symm_hom,
        NatIso.ofComponents_inv_app, Iso.refl_inv]
      erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      exact comparison_coefficients_cube X V q N) M
  simpa only [comparisonDerivedSliceCoefficients, sliceRestrictScalarsIso,
    comparisonRestrictScalarsIso, derivedComparisonSliceIso,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc] using h
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

end AlgebraicGeometry.Scheme
