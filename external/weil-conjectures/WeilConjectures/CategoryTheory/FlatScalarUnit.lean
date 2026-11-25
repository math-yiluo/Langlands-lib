/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ExactDegreeZero
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape

/-! # Flat ordinary scalar units compute derived scalar units

Source: Stacks Project, sites-cohomology, K-flat resolutions and derived change of rings.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SheafExactDegreeZero

attribute [local instance 10000] scalarWeakSheafify

open MonoidalCategory

private noncomputable def moduleExtendRestrictIso
    {R A : Type (u + 1)} [CommRing R] [CommRing A] (φ : R →+* A) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} A) ⋙
      ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ ≅
      tensorLeft ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of A A)) :=
  NatIso.ofComponents (fun M ↦
    (show (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).obj M) ≃ₗ[R]
        (tensorLeft ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj
          (ModuleCat.of A A))).obj M from
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ by rfl }).toModuleIso) (by
    intro M N f
    ext a
    rfl)

private noncomputable def extensionRestrictIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) :
    Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ) ⋙
      Sheaf.restrictScalars J φ ≅
      tensorLeft ((presheafToSheaf J (ModuleCat.{u + 1} R)).obj
        ((Functor.const Cᵒᵖ).obj
          ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of A A)))) := by
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of A A)
  let P := (Functor.const Cᵒᵖ).obj B
  let L := presheafToSheaf J (ModuleCat.{u + 1} R)
  let U := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ
  let E := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ
  letI : U.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint
  letI : J.PreservesSheafification U :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let i := sheafComposeNatIso J U
    (sheafificationAdjunction J (ModuleCat.{u + 1} A))
    (sheafificationAdjunction J (ModuleCat.{u + 1} R))
  let j : (Functor.whiskeringRight Cᵒᵖ _ _).obj E ⋙
      (Functor.whiskeringRight Cᵒᵖ _ _).obj U ≅ tensorLeft P :=
    NatIso.ofComponents (fun F ↦ NatIso.ofComponents
      (fun X ↦ (moduleExtendRestrictIso φ).app (F.obj X))
      (fun f ↦ (moduleExtendRestrictIso φ).hom.naturality (F.map f)))
      (by
        intro F G f
        apply NatTrans.ext
        funext X
        exact (moduleExtendRestrictIso φ).hom.naturality (f.app X))
  exact Functor.isoWhiskerLeft
      (sheafToPresheaf J (ModuleCat.{u + 1} R) ⋙
        (Functor.whiskeringRight Cᵒᵖ _ _).obj E) i.symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{u + 1} R)) j) L ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{u + 1} R))
      (Sheaf.presheafToSheafCompTensorLeftIso P).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J _).counit)
      (tensorLeft (L.obj P)) ≪≫ (tensorLeft (L.obj P)).leftUnitor

private theorem extension_additive
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) :
    (Sheaf.composeAndSheafify J
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).Additive :=
  (Sheaf.adjunction J
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)).left_adjoint_additive

attribute [local instance] extension_additive

private theorem extension_preservesKFlatQuasiIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) :
    (Sheaf.composeAndSheafify J
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).PreservesKFlatQuasiIso := by
  let E := Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let U := Sheaf.restrictScalars J φ
  let : E.Additive := extension_additive.{u} J φ
  let : (E ⋙ U).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive (E ⋙ U)
  let B := (presheafToSheaf J (ModuleCat.{u + 1} R)).obj
    ((Functor.const Cᵒᵖ).obj
      ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of A A)))
  apply Functor.PreservesKFlatQuasiIso.mk'
  intro K hK hKa
  have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa B
  have hl := ht.of_iso
    ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight B) _).app K).symm
  have he : (((E ⋙ U).mapHomologicalComplex _).obj K).Acyclic :=
    hl.of_iso ((NatIso.mapHomologicalComplex (extensionRestrictIso.{u} J φ) _).app K).symm
  intro n
  exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (he n)

section SingleNormalization

variable {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
  (E : V ⥤ W) (U : W ⥤ V) [E.Additive] [U.Additive]

private theorem single_unit_square (a : E ⊣ U) (F : V) :
    (a.mapHomologicalComplex (.up ℤ)).unit.app
        ((HomologicalComplex.single V (.up ℤ) 0).obj F) ≫
      (U.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app F) ≫
      (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app (E.obj F) =
    (HomologicalComplex.single V (.up ℤ) 0).map (a.unit.app F) := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      CategoryTheory.Functor.map_id, Category.id_comp]
    change a.unit.app F ≫ U.map (𝟙 (E.obj F)) ≫ 𝟙 (U.obj (E.obj F)) =
      a.unit.app F ≫ 𝟙 (U.obj (E.obj F))
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 F i hi).eq_of_src _ _

variable [HasDerivedCategory V] [HasDerivedCategory W]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

private theorem derived_single_unit_square (a : E ⊣ U) (F : V) :
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app
        ((HomologicalComplex.single V (.up ℤ) 0).obj F)) ≫
      U.mapDerivedCategoryFactors.inv.app
        ((E.mapHomologicalComplex (.up ℤ)).obj
          ((HomologicalComplex.single V (.up ℤ) 0).obj F)) ≫
      U.mapDerivedCategory.map (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app F)) =
    (DerivedCategory.singleFunctor V 0).map (a.unit.app F) ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj F) := by
  erw [← U.mapDerivedCategoryFactors.inv.naturality]
  apply (cancel_mono ((U.mapDerivedCategorySingleFunctor 0).hom.app (E.obj F))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [U.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
  dsimp only [Functor.comp_map, Functor.comp_obj]
  erw [Category.comp_id, ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  exact congrArg DerivedCategory.Q.map (single_unit_square E U a F)

end SingleNormalization

section FlatAdjunction

universe v
variable {V W : Type*} [Category.{v} V] [Category.{v} W] [Abelian V] [Abelian W]
  [IsGrothendieckAbelian.{v} V] [IsGrothendieckAbelian.{v} W]
  [HasDerivedCategory.{v} V] [HasDerivedCategory.{v} W]
  [MonoidalCategory V] [MonoidalPreadditive V] [MonoidalClosed V] [BraidedCategory V]
  [Abelian.HasFunctorialFlatResolution V]
  (E : V ⥤ W) (U : W ⥤ V) [E.Additive] [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

private theorem universal_of_flat_adjoint [E.PreservesKFlatQuasiIso] (a : E ⊣ U) (F : V) (G : W)
    (η : F ⟶ U.obj G) (hF : ObjectProperty.flat F)
    (hη : ∀ H : W, Function.Bijective (fun f : G ⟶ H ↦ η ≫ U.map f)) :
    Universal U η := by
  let b := a.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let X := (HomologicalComplex.single V (.up ℤ) 0).obj F
  let c := DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app F)
  let δ := DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
    U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X)
  have hδ : IsIso ((b.homEquiv _ _).symm δ) :=
    Adjunction.isIso_cochainTranspose_of_kFlat E U a b X
      ((CochainComplex.kFlat_single_obj_iff_flat F 0).2 hF)
  let t : E.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor V 0).obj F) ⟶
      (DerivedCategory.singleFunctor W 0).obj (E.obj F) := (b.homEquiv _ _).symm
    ((DerivedCategory.singleFunctor V 0).map (a.unit.app F) ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj F))
  have ht : t = (b.homEquiv _ _).symm δ ≫ c.hom := by
    rw [← Adjunction.homEquiv_naturality_right_symm]
    apply congrArg (b.homEquiv _ _).symm
    simpa only [δ, c, X, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
      (derived_single_unit_square E U a F).symm
  have htiso : IsIso t := by rw [ht]; infer_instance
  let q := (a.homEquiv _ _).symm η
  have hq : IsIso q := by
    apply isIso_of_coyoneda_map_bijective
    intro H
    have he : (fun f : G ⟶ H ↦ a.homEquiv F H (q ≫ f)) =
        (fun f : G ⟶ H ↦ η ≫ U.map f) := by
      funext f
      rw [Adjunction.homEquiv_naturality_right]
      simp only [q, Equiv.apply_symm_apply]
    have hb : Function.Bijective (fun f : G ⟶ H ↦ a.homEquiv F H (q ≫ f)) :=
      he ▸ hη H
    exact (Function.Bijective.of_comp_iff' (a.homEquiv F H).bijective _).mp hb
  have hηq : a.unit.app F ≫ U.map q = η := by
    calc
      _ = a.homEquiv F G q := (a.homEquiv_unit F G q).symm
      _ = η := (a.homEquiv F G).apply_symm_apply η
  have hraw : (DerivedCategory.singleFunctor V 0).map η ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app G =
    ((DerivedCategory.singleFunctor V 0).map (a.unit.app F) ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj F)) ≫
      U.mapDerivedCategory.map ((DerivedCategory.singleFunctor W 0).map q) := by
    rw [← hηq, Functor.map_comp]
    simpa only [Functor.comp_map, Category.assoc] using congrArg
      ((DerivedCategory.singleFunctor V 0).map (a.unit.app F) ≫ ·)
      ((U.mapDerivedCategorySingleFunctor 0).inv.naturality q)
  apply (universal_iff U η).mpr
  intro N
  let k := t ≫ (DerivedCategory.singleFunctor W 0).map q
  have hk : IsIso k := by dsimp only [k]; infer_instance
  convert (b.homEquiv _ N).bijective.comp
    ((asIso k).symm.homFromEquiv (Z := N)).bijective using 1
  funext f
  change _ = b.homEquiv _ N (k ≫ f)
  rw [Adjunction.homEquiv_naturality_right]
  dsimp only [k]
  rw [Adjunction.homEquiv_naturality_right]
  simp only [t, Equiv.apply_symm_apply]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ U.mapDerivedCategory.map f) hraw

end FlatAdjunction

/-- A flat source lets an ordinary scalar-extension unit compute the unbounded derived unit.
Source: Stacks Project, sites-cohomology, lemma-bounded-flat-K-flat,
lemma-derived-base-change, and lemma-adjoint, applied to a change of constant rings.
(auxiliary; not a blueprint node).

Proof: Let E be sheafified sectionwise extension of scalars along φ, left adjoint to
restriction. Restriction is exact and conservative. Its composite with E is tensoring
with the constant R-module A. Thus E preserves quasi-isomorphisms between K-flat
complexes, by the tensor criterion for K-flatness. Derive this adjunction on unbounded
complexes. Flatness of F makes F[0] K-flat, so the derived counit identifies LE(F[0])
with (EF)[0]. The ordinary Hom bijections say that the adjunction transpose EF → G
of η is invertible: both EF and G represent Hom(F, res(-)). Compose the K-flat
comparison with this isomorphism. The derived adjunction then gives the asserted
bijections for every unbounded test complex. Naturality of the derived counit on
single complexes identifies its unit with scalarUnit(η), including the exact-single
comparison. This uses flatness of F alone, never flatness of A over R. -/
theorem scalarUniversal_of_flat
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) (F : Sheaf J (ModuleCat.{u + 1} R))
    (G : Sheaf J (ModuleCat.{u + 1} A))
    (η : F ⟶ (Sheaf.restrictScalars J φ).obj G)
    (hF : ObjectProperty.flat F)
    (hη : ∀ H : Sheaf J (ModuleCat.{u + 1} A),
      Function.Bijective (fun f : G ⟶ H ↦ η ≫ (Sheaf.restrictScalars J φ).map f)) :
    scalarUniversal J φ F G η := by
  let E := Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let : E.PreservesKFlatQuasiIso := extension_preservesKFlatQuasiIso J φ
  unfold scalarUniversal scalarUnit scalarObj Sheaf.IsDerivedBaseChange
  change Universal (Sheaf.restrictScalars J φ) η
  exact universal_of_flat_adjoint E (Sheaf.restrictScalars J φ)
    (Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)) F G η hF hη

end SheafExactDegreeZero
