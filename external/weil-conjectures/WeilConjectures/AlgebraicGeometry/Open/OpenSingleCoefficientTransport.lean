/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseSingleMapComposition
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import all WeilConjectures.AlgebraicGeometry.OpenPinnedSingleTensorRestrictionFactors
import WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit

/-! # Coefficient transport along an isomorphic apex over an open subscheme

## References

* Stacks Project, Tags 06YJ and 0D5S
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

set_option linter.flexible false in
-- The degree-zero single-object identifications are normalized before changing the goal.
private theorem single_iso_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (M : C) :
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app M =
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
      (HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app M) := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      HomologicalComplex.single_map_f_self]
    change e.hom.app M ≫ 𝟙 _ = 𝟙 _ ≫ e.hom.app M ≫ 𝟙 _
    simp only [Category.id_comp]
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne, hi]

private theorem cancel {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
      {X Y : D} {U V : C} (e : X ⟶ Y) (q : Y ⟶ F.obj U) (b : U ≅ V) :
      (e ≫ q ≫ F.map b.hom) ≫ F.map b.inv = e ≫ q := by
  simp only [Category.assoc, ← F.map_comp, b.hom_inv_id, F.map_id, Category.comp_id]

private theorem mapIdentityCounit
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ E) (Q : D ⥤ E) {A : C} {B : D} (e : L.obj A ⟶ Q.obj B) :
    L.map (𝟙 A) ≫ e ≫ Q.map (𝟙 B) ≫ 𝟙 (Q.obj B) = e := by
  simp only [L.map_id, Q.map_id, Category.comp_id, Category.id_comp]

-- Keep square pasting and cancellation in an abstract category.
private theorem paste_square {C : Type*} [Category C]
    {A B D E F G : C} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ E} {d : E ⟶ D}
    {e : D ⟶ G} {f : E ⟶ F} {g : F ⟶ G}
    (h : a ≫ b = c ≫ d) (h' : d ≫ e = f ≫ g) :
    a ≫ b ≫ e = c ≫ f ≫ g := by
  rw [← Category.assoc, h, Category.assoc, h']

-- Lift single-complex naturality before specializing the module categories.
private theorem single_derived_iso_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory D] {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (M : C) :
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
        ((HomotopyCategory.singleFunctor C 0).obj M)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app M)) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)) ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app M) := by
  have h := congrArg (fun f ↦ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient D (.up ℤ)).map f)) (single_iso_naturality e M)
  simp only [Functor.map_comp] at h
  exact h

private theorem single_derived_map_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] {M N : C} (m : M ⟶ N) :
    DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.singleFunctor C 0).map m)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app N)) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)) ≫
      (DerivedCategory.singleFunctor D 0).map (F.map m) := by
  have h := congrArg (fun f ↦ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient D (.up ℤ)).map f))
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.naturality m)
  dsimp only [Functor.comp_map] at h
  simp only [DerivedCategory.singleFunctor, DerivedCategory.singleFunctors,
    HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
    SingleFunctors.postcomp, CochainComplex.singleFunctors,
    Functor.comp_map]
  erw [Functor.mapHomotopyCategory_map]
  simp only [Functor.map_comp, Functor.comp_obj] at h
  exact h

-- Paste the coefficient diagram with its comparison maps kept abstract.
private theorem transport_paste {C : Type*} [Category C]
    {A B D E F G H I J K L : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E} {d : E ⟶ G}
    {p : A ⟶ F} {q : F ⟶ G} {k : G ⟶ L}
    (s : H ≅ D) {e : E ⟶ J} {i : H ⟶ I} {j : I ⟶ J}
    {l : J ⟶ L} {m : I ⟶ K} {n : K ⟶ L} {t : H ⟶ K}
    (h₁ : a ≫ b ≫ c ≫ d = p ≫ q)
    (h₂ : s.hom ≫ c ≫ e = i ≫ j)
    (hb : d ≫ k = e ≫ l) (hn : m ≫ n = j ≫ l) (ha : t = i ≫ m) :
    p ≫ q ≫ k = a ≫ b ≫ s.inv ≫ t ≫ n := by
  have h₂' : c ≫ e = s.inv ≫ i ≫ j := by
    rw [← h₂]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [← Category.assoc, ← h₁]
  simp only [Category.assoc]
  rw [hb, reassoc_of% h₂', ← hn, ha]
  simp only [Category.assoc]

-- Factor the inverse uniqueness comparison without expanding its construction.
private theorem leftDerivedUnique_inv_app
    {C D H : Type*} [Category C] [Category D] [Category H]
    (LF' LF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D}
    (α : L ⋙ LF ⟶ F) (α' : L ⋙ LF' ⟶ F) (W : MorphismProperty C)
    [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W]
    [LF'.IsLeftDerivedFunctor α' W] (P : C) :
    (Functor.leftDerivedUnique LF' LF α α' W).inv.app (L.obj P) ≫ α.app P =
      α'.app P := by
  simpa only [Functor.leftDerivedUnique, Functor.leftDerivedNatIso_inv,
    Iso.refl_inv, NatTrans.id_app, Category.comp_id] using
    (Functor.leftDerivedNatTrans_app LF' LF α' α W (𝟙 _) P)

variable [dc : ∀ Y : Scheme.{u}, HasDerivedCategory.{u + 1}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

private instance tensorAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (show SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) from
        Scheme.Modules.tensorPullback f).Additive :=
  Scheme.Modules.canonicalTensorPullbackAdditive f

attribute [local irreducible]
  Scheme.Modules.tensorPullbackCompositionIso Scheme.Modules.tensorPullback

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules.Hom DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh

set_option cleanup.letToHave false in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem open_counit_factor
    (X : Scheme.{u}) (U : X.Opens)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (singleComplexOpenPullbackIso X U).inv.app (DerivedCategory.Qh.obj P) ≫
        (SingleComplexBaseChange.counit.{u, u + 1} U.ι).app P =
      (schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (openPinnedTensorOpenIso X U).inv (.up ℤ)).app P) := by
  classical
  let T : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback U.ι
  let e : schemeOpenRestriction X U ≅ T := Scheme.Modules.overFunctorEquiv U ≪≫
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm).symm
  have : PreservesFiniteLimits (schemeOpenRestriction X U) :=
    schemeOpenRestriction_preservesFiniteLimits X U
  have : PreservesFiniteColimits (schemeOpenRestriction X U) :=
    schemeOpenRestriction_preservesFiniteColimits X U
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso e
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  have hL : (derivedPullback U.ι).IsLeftDerivedFunctor
      (SingleComplexBaseChange.counit.{u, u + 1} U.ι) W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) U.ι
  have := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let ε := SingleComplexBaseChange.counit.{u, u + 1} U.ι
  let l := Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback U.ι)
    ε T.mapDerivedCategoryFactorsh.hom W
  have hf : l.inv.app (DerivedCategory.Qh.obj P) ≫ ε.app P =
      T.mapDerivedCategoryFactorsh.hom.app P := by
    exact leftDerivedUnique_inv_app T.mapDerivedCategory (derivedPullback U.ι)
      ε T.mapDerivedCategoryFactorsh.hom W P
  dsimp only [singleComplexOpenPullbackIso, Iso.trans_inv, NatTrans.comp_app]
  simp only [Iso.symm_inv, Category.assoc]
  change (Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Qh.obj P) ≫
    l.inv.app (DerivedCategory.Qh.obj P) ≫ ε.app P = _
  rw [hf, Functor.mapDerivedCategoryNatIso_fach]
  have hθ : e.hom = (openPinnedTensorOpenIso X U).inv := by
    simp only [e, openPinnedTensorOpenIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rw [hθ]

set_option cleanup.letToHave false in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem q_normalize {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    Scheme.picardTermwiseSingleMap f M =
      (SingleComplexBaseChange.counit.{u,u+1} f).app ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.tensorPullback f) (.up ℤ) 0).hom.app M)) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  simp only [Scheme.picardTermwiseSingleMap, Scheme.Modules.canonicalSinglePullbackMap,
    cast_eq, Scheme.Modules, Scheme.ringCatSheaf, moduleRings,
    Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id, SingleComplexBaseChange.counit]

attribute [local irreducible] singleComplexOpenPullbackIso Scheme.picardTermwiseSingleMap
  Scheme.picardTermwiseCounit

set_option cleanup.letToHave false in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem open_single_factor (Y : Scheme.{u}) (U : Y.Opens) (M : Y.Modules) :
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
    let ρ := (openPinnedTensorOpenIso Y U).app M ≪≫ (Scheme.Modules.overFunctorEquiv U).app M
    (singleComplexOpenPullbackIso Y U).hom.app K ≫
      ((schemeOpenRestriction Y U).mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor _ 0).map ((Scheme.Modules.overFunctorEquiv U).hom.app M) =
    Scheme.picardTermwiseSingleMap U.ι M ≫ (DerivedCategory.singleFunctor _ 0).map ρ.hom := by
  classical
  dsimp only
  rw [q_normalize]
  apply (cancel_epi ((singleComplexOpenPullbackIso Y U).inv.app _)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have ho := open_counit_factor Y U ((HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)
  change (singleComplexOpenPullbackIso Y U).inv.app
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ≫ _ = _ at ho
  rw [← Category.assoc ((singleComplexOpenPullbackIso Y U).inv.app _), ho]
  have hh := single_derived_iso_naturality (openPinnedTensorOpenIso Y U).symm M
  simp only [Iso.symm_hom] at hh
  have hs := (open_pinned_single_tensor_restriction_factors
    (𝟙 Y) U U (𝟙 U.toScheme) (by simp) M).1
  simp only [Category.assoc]
  erw [reassoc_of% hh]
  rw [← Functor.map_comp]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc, hs]

set_option cleanup.letToHave false in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem counit_normalize {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    (Scheme.picardTermwiseCounit f).app K =
      (SingleComplexBaseChange.counit.{u,u+1} f).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) := by
  simp only [Scheme.picardTermwiseCounit, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  exact mapIdentityCounit (derivedPullback f) DerivedCategory.Qh _

attribute [local irreducible] SingleComplexBaseChange.counit

set_option cleanup.letToHave false in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem q_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (m : M ⟶ N) :
    (derivedPullback f).map ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map m) ≫
      Scheme.picardTermwiseSingleMap f N =
    Scheme.picardTermwiseSingleMap f M ≫ (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
        ((Scheme.Modules.tensorPullback f).map m) := by
  simp only [q_normalize f N, q_normalize f M, Category.assoc]
  have hn := (SingleComplexBaseChange.counit.{u,u+1} f).naturality
    ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map m)
  change (derivedPullback f).map ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map m) ≫ _ = _ at hn
  refine paste_square hn ?_
  exact single_derived_map_naturality (Scheme.Modules.tensorPullback f) m

set_option cleanup.letToHave false in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem q_composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : X ⟶ Z) (ht : f ≫ g = t) (M : Z.Modules) :
    (relativeMVComp f g).hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M) ≫
      eqToHom (congrArg (fun a ↦ (derivedPullback a).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M)) ht) ≫
      Scheme.picardTermwiseSingleMap t M ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
          ((Scheme.Modules.tensorPullbackCompositionIso f g t ht).hom.app M) =
    (derivedPullback f).map (Scheme.picardTermwiseSingleMap g M) ≫
      Scheme.picardTermwiseSingleMap f ((Scheme.Modules.tensorPullback g).obj M) := by
  subst t
  simp only [eqToHom_refl, Category.id_comp]
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
  let z := DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.tensorPullback f) (.up ℤ) 0).app
      ((Scheme.Modules.tensorPullback g).obj M))
  let c := relativeMVComp f g
  have h := Scheme.picardTermwiseSingleMap_composition f g (f ≫ g) rfl M
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, eqToIso_refl, Iso.trans_refl] at h
  change c.hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M) ≫
      Scheme.picardTermwiseSingleMap (f ≫ g) M ≫
      S.map ((Scheme.Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl).hom.app M) ≫ z.inv =
    (derivedPullback f).map (Scheme.picardTermwiseSingleMap g M) ≫
      (Scheme.picardTermwiseCounit f).app ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback g).obj M)) at h
  have hh := congrArg (fun a ↦ a ≫ z.hom) h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  rw [counit_normalize] at hh
  have hq := q_normalize f ((Scheme.Modules.tensorPullback g).obj M)
  change Scheme.picardTermwiseSingleMap f ((Scheme.Modules.tensorPullback g).obj M) =
    (SingleComplexBaseChange.counit.{u,u+1} f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback g).obj M))) ≫ z.hom at hq
  rw [← hq] at hh
  simpa only [S, c, z, Functor.mapIso_hom, Category.assoc] using hh

set_option cleanup.letToHave false in
-- Keep the selected derived comparisons abstract during this calculation.
private theorem q_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    IsIso (Scheme.picardTermwiseSingleMap f M) := by
  rw [q_normalize]
  have hc := SingleComplexBaseChange.isIso_counit_of_isIso f
    ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)
  change IsIso ((SingleComplexBaseChange.counit.{u,u+1} f).app
    ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)) at hc
  infer_instance

set_option cleanup.letToHave false in
-- The selected counits have large dependent types; keep their data abstract.
/-- The single-complex coefficient square for restriction and an isomorphic apex. -/
theorem exists_openSingle_coefficient_transport
    {Y P P' : Scheme.{u}} (U : Y.Opens) (M : Y.Modules)
    (r : P ⟶ Y) (r' : P' ⟶ U.toScheme) (k : P' ≅ P)
    (hr : k.hom ≫ r = r' ≫ U.ι) :
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
    let N := M.restrict U.ι
    let a : (derivedPullback U.ι).obj K ≅
        (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj N :=
      (singleComplexOpenPullbackIso Y U).app K ≪≫
        ((schemeOpenRestriction Y U).mapDerivedCategorySingleFunctor 0).app M ≪≫
        (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).mapIso
          ((Scheme.Modules.overFunctorEquiv U).app M)
    let T := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj
      ((Scheme.Modules.tensorPullback r).obj M)
    let T' := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings P'.toRingedSpace)) 0).obj
      ((Scheme.Modules.tensorPullback r').obj N)
    ∃ d : (derivedPullback k.hom).obj T ≅ T',
      (derivedPullback k.hom).map (Scheme.picardTermwiseSingleMap r M) ≫ d.hom =
        (relativeMVComp k.hom r).hom.app K ≫
          eqToHom (congrArg (fun f ↦ (derivedPullback f).obj K) hr) ≫
          (relativeMVComp r' U.ι).inv.app K ≫ (derivedPullback r').map a.hom ≫
          Scheme.picardTermwiseSingleMap r' N := by
  classical
  dsimp only
  let δ₁ := (Scheme.Modules.tensorPullbackCompositionIso k.hom r (r' ≫ U.ι) hr).app M
  let δ₂ := (Scheme.Modules.tensorPullbackCompositionIso r' U.ι (r' ≫ U.ι) rfl).app M
  let ρ := (openPinnedTensorOpenIso Y U).app M ≪≫ (Scheme.Modules.overFunctorEquiv U).app M
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings P'.toRingedSpace)) 0
  let b := δ₁.symm ≪≫ δ₂ ≪≫ (Scheme.Modules.tensorPullback r').mapIso ρ
  have : IsIso (Scheme.picardTermwiseSingleMap k.hom
      ((Scheme.Modules.tensorPullback r).obj M)) := q_isIso _ _
  refine ⟨asIso (Scheme.picardTermwiseSingleMap k.hom
    ((Scheme.Modules.tensorPullback r).obj M)) ≪≫ S.mapIso b, ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  have h₁ := q_composition k.hom r (r' ≫ U.ι) hr M
  have h₂ := q_composition r' U.ι (r' ≫ U.ι) rfl M
  have hρ := q_naturality r' ρ.hom
  have ha := open_single_factor Y U M
  simp only [eqToHom_refl, Category.id_comp] at h₂
  have hb : S.map δ₁.hom ≫ S.map b.hom =
      S.map δ₂.hom ≫ S.map ((Scheme.Modules.tensorPullback r').map ρ.hom) := by
    rw [← S.map_comp, ← S.map_comp]
    congr 1
    simp only [b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.hom_inv_id_assoc]
  have ha' := congrArg ((derivedPullback r').map) ha
  simp only [Functor.map_comp] at ha'
  exact transport_paste ((relativeMVComp r' U.ι).app
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)) h₁ h₂ hb hρ
    (by simpa only [Functor.map_comp, Iso.app_hom] using ha')

end AlgebraicGeometry
