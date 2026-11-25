/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Free
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.AlgebraicGeometry.SiteLocallyConstantFiniteType
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.SliceTensorNatural
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Comparing tensor cohomology with local finite free models

Source: Stacks Project, Cohomology on Sites, Tag 094H
(auxiliary; not a blueprint node).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
set_option autoImplicit false
set_option synthInstance.maxSize 256

noncomputable section

section Generic
universe w v u
variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory.{w} A]

omit [IsGrothendieckAbelian A] [MonoidalCategory A] [MonoidalPreadditive A]
  [MonoidalClosed A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A] in
private theorem homology_iso_of_upper_triangle (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang _) (i : ℤ) [T.obj₁.IsLE (i - 1)] :
    IsIso ((DerivedCategory.homologyFunctor A i).map T.mor₂) := by
  let H := DerivedCategory.homologyFunctor A 0
  have h₀ := DerivedCategory.isZero_of_isLE T.obj₁ (i - 1) i (by omega)
  have h₁ := DerivedCategory.isZero_of_isLE T.obj₁ (i - 1) (i + 1) (by omega)
  have : Mono ((H.shift i).map T.mor₂) :=
    (H.homologySequence_mono_shift_map_mor₂_iff T hT i).2 (h₀.eq_of_src _ _)
  have : Epi ((H.shift i).map T.mor₂) :=
    (H.homologySequence_epi_shift_map_mor₂_iff T hT i (i + 1) rfl).2
      (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((H.shift i).map T.mor₂)

end Generic

section Compare
universe wA wD vA vD uA uD
variable {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory.{wA} A]
  {D : Type uD} [Category.{vD} D] [Abelian D] [IsGrothendieckAbelian.{vD} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory.{wD} D]

omit [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory A] in
private theorem kflat_of_acyclic (P : CochainComplex A ℤ)
    (hP : ∀ Z : CochainComplex A ℤ, Z.Acyclic → (Z ⊗ P).Acyclic) :
    (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro Z hZ
  obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (Z ⊗ P)).2 (hP Z hZ)
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr

omit [HasDerivedCategory A] in
private theorem bounded_flat_model (P : CochainComplex A ℤ) (b : ℤ) [P.IsLE b] :
    ∃ (L : CochainComplex A ℤ) (_ : L.IsStrictlyLE b) (f : L ⟶ P),
      QuasiIso f ∧ ∀ n, ObjectProperty.flat (L.X n) := by
  obtain ⟨L, hL, f, hf, hflat⟩ := (P.truncLE b).exists_quasiIso_flat_of_isStrictlyLE b
  exact ⟨L, hL, f ≫ P.ιTruncLE b, inferInstance, hflat⟩

omit [HasDerivedCategory A] in
private theorem tensor_image_compare
    (V : A ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesColimitsOfSize.{0, 0} V]
    (hflat : ∀ X : A, ObjectProperty.flat X → ObjectProperty.flat (V.obj X))
    (τ : (Functor.postcompose₂.obj V).obj (curriedTensor A) ≅
      (((Functor.whiskeringLeft₂ D).obj V).obj V).obj (curriedTensor D))
    (P Q : CochainComplex A ℤ) (b c : ℤ) [P.IsLE b] [Q.IsLE c]
    (_hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat Q) :
    Nonempty (DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q)) ≅
      DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj P) ⊗
        DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj Q)) := by
  obtain ⟨L, hL, f, hf, hfL⟩ := bounded_flat_model P b
  obtain ⟨M, hM, g, hg, hfM⟩ := bounded_flat_model Q c
  have hLk := CochainComplex.kFlat_of_isStrictlyLE_of_flat L b hfL
  have hMk := CochainComplex.kFlat_of_isStrictlyLE_of_flat M c hfM
  have hfq : QuasiIso (f ▷ Q) := (CochainComplex.kFlat_iff_preservesQuasiIso Q).1 hQ |>.2 f hf
  have hlg : QuasiIso (L ◁ g) := (CochainComplex.kFlat_iff_preservesQuasiIso L).1 hLk |>.1 g hg
  let W := V.mapHomologicalComplex (.up ℤ)
  have : IsIso (DerivedCategory.Q.map (W.map (f ▷ Q))) := by infer_instance
  have : IsIso (DerivedCategory.Q.map (W.map (L ◁ g))) := by infer_instance
  let e := asIso (HomologicalComplex.mapBifunctorComparison τ.hom (.up ℤ) L M)
  have hVL : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat (W.obj L) :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat (W.obj L) b (fun n ↦ hflat _ (hfL n))
  have : IsIso (DerivedCategory.Q.map (W.map f)) := by infer_instance
  have : IsIso (DerivedCategory.Q.map (W.map g)) := by infer_instance
  exact ⟨(asIso (DerivedCategory.Q.map (W.map (f ▷ Q)))).symm ≪≫
    (asIso (DerivedCategory.Q.map (W.map (L ◁ g)))).symm ≪≫
    DerivedCategory.Q.mapIso e ≪≫
    (DerivedCategory.QObjTensorQObjIsoOfKFlatLeft (W.obj L) (W.obj M) hVL).symm ≪≫
    tensorIso (asIso (DerivedCategory.Q.map (W.map f)))
      (asIso (DerivedCategory.Q.map (W.map g)))⟩
omit [IsGrothendieckAbelian A] [MonoidalCategory A] [MonoidalPreadditive A]
  [MonoidalClosed A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A] in
private theorem tensor_truncGE_image_left
    (V : A ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (P : CochainComplex A ℤ) (N : DerivedCategory D) (b i : ℤ) [N.IsLE b] :
    Nonempty ((DerivedCategory.homologyFunctor D i).obj
      (DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj P) ⊗ N) ≅
      (DerivedCategory.homologyFunctor D i).obj
        (DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj
          (P.truncGE (i - b))) ⊗ N)) := by
  let a := i - b
  let S := P.shortComplexTruncLE_shortExact (a - 1)
  let T := DerivedCategory.triangleOfSES S
  let F := V.mapDerivedCategory ⋙ tensorRight N
  have hb : T.obj₁.IsLE (a - 1) := by
    change (DerivedCategory.Q.obj (P.truncLE (a - 1))).IsLE (a - 1)
    infer_instance
  have hb' := V.isLE_mapDerivedCategory_obj T.obj₁ (a - 1)
  have : (F.mapTriangle.obj T).obj₁.IsLE (i - 1) := by
    have h := DerivedCategory.isLE_tensor (V.mapDerivedCategory.obj T.obj₁) N (a - 1) b
    convert h using 1 <;> dsimp [F, a]
    omega
  have hT := F.map_distinguished T (DerivedCategory.triangleOfSES_distinguished S)
  have : IsIso ((DerivedCategory.homologyFunctor D i).map (F.map T.mor₂)) :=
    homology_iso_of_upper_triangle (F.mapTriangle.obj T) hT i
  let f := P.shortComplexTruncLEX₃ToTruncGE (a - 1) a (by omega)
  have : IsIso (DerivedCategory.Q.map f) := inferInstance
  let e := asIso ((DerivedCategory.homologyFunctor D i).map (F.map T.mor₂)) ≪≫
    (DerivedCategory.homologyFunctor D i).mapIso
      (F.mapIso (asIso (DerivedCategory.Q.map f)))
  exact ⟨(DerivedCategory.homologyFunctor D i).mapIso
      (whiskerRightIso (V.mapDerivedCategoryFactors.app P).symm N) ≪≫ e ≪≫
    (DerivedCategory.homologyFunctor D i).mapIso
      (whiskerRightIso (V.mapDerivedCategoryFactors.app (P.truncGE a)) N)⟩

omit [IsGrothendieckAbelian A] [MonoidalCategory A] [MonoidalPreadditive A]
  [MonoidalClosed A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A] in
private theorem tensor_truncGE_image_right
    (V : A ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (P : CochainComplex A ℤ) (N : DerivedCategory D) (b i : ℤ) [N.IsLE b] :
    Nonempty ((DerivedCategory.homologyFunctor D i).obj
      (N ⊗ DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj P)) ≅
      (DerivedCategory.homologyFunctor D i).obj
        (N ⊗ DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj
          (P.truncGE (i - b))))) := by
  let a := i - b
  let S := P.shortComplexTruncLE_shortExact (a - 1)
  let T := DerivedCategory.triangleOfSES S
  let F := V.mapDerivedCategory ⋙ tensorLeft N
  have hb : T.obj₁.IsLE (a - 1) := by
    change (DerivedCategory.Q.obj (P.truncLE (a - 1))).IsLE (a - 1)
    infer_instance
  have hb' := V.isLE_mapDerivedCategory_obj T.obj₁ (a - 1)
  have : (F.mapTriangle.obj T).obj₁.IsLE (i - 1) := by
    have h := DerivedCategory.isLE_tensor N (V.mapDerivedCategory.obj T.obj₁) b (a - 1)
    convert h using 1 <;> dsimp [F, a]
    omega
  have hT := F.map_distinguished T (DerivedCategory.triangleOfSES_distinguished S)
  have : IsIso ((DerivedCategory.homologyFunctor D i).map (F.map T.mor₂)) :=
    homology_iso_of_upper_triangle (F.mapTriangle.obj T) hT i
  let f := P.shortComplexTruncLEX₃ToTruncGE (a - 1) a (by omega)
  have : IsIso (DerivedCategory.Q.map f) := inferInstance
  let e := asIso ((DerivedCategory.homologyFunctor D i).map (F.map T.mor₂)) ≪≫
    (DerivedCategory.homologyFunctor D i).mapIso
      (F.mapIso (asIso (DerivedCategory.Q.map f)))
  exact ⟨(DerivedCategory.homologyFunctor D i).mapIso
      (whiskerLeftIso N (V.mapDerivedCategoryFactors.app P).symm) ≪≫ e ≪≫
    (DerivedCategory.homologyFunctor D i).mapIso
      (whiskerLeftIso N (V.mapDerivedCategoryFactors.app (P.truncGE a)))⟩

end Compare

section Curried
universe vA vD uA uD
variable {A : Type uA} [Category.{vA} A] [MonoidalCategory A]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
@[irreducible]
private def curried_tensor_iso (V : A ⥤ D)
    (e : tensor A ⋙ V ≅ V.prod V ⋙ tensor D) :
    (Functor.postcompose₂.obj V).obj (curriedTensor A) ≅
      (((Functor.whiskeringLeft₂ D).obj V).obj V).obj (curriedTensor D) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ e.app (M, N)) (by
    intro N N' g
    have h := e.hom.naturality (X := (M, N)) (Y := (M, N')) (𝟙 M, g)
    change V.map (𝟙 M ⊗ₘ g) ≫ _ = _ ≫ (V.map (𝟙 M) ⊗ₘ V.map g) at h
    change V.map (M ◁ g) ≫ _ = _ ≫ (V.obj M ◁ V.map g)
    simpa only [V.map_id, id_tensorHom, Iso.app_hom] using h)) (by
      intro M M' f
      apply NatTrans.ext
      funext N
      have h := e.hom.naturality (X := (M, N)) (Y := (M', N)) (f, 𝟙 N)
      change V.map (f ⊗ₘ 𝟙 N) ≫ _ = _ ≫ (V.map f ⊗ₘ V.map (𝟙 N)) at h
      change V.map (f ▷ N) ≫ _ = _ ≫ (V.map f ▷ V.obj N)
      simpa only [V.map_id, tensorHom_id, Iso.app_hom, NatIso.ofComponents_hom_app] using h)
end Curried

section Site
universe u
variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (B : Type u) [CommRing B]
open SheafOfModules
local notation "ℛ" => realizationRing J B
local notation "A" => realizationModules J B
set_option hygiene false in
set_option quotPrecheck false in
local notation "V" U => overFunctor.{u} ((sheafCompose J
  (forget₂ CommRingCat.{u} RingCat.{u})).obj ℛ) U
local notation "cB" => commutativeSiteConstantModuleFunctor J B

noncomputable local instance siteTensorLocalModelMonoidal :
    MonoidalCategory A := monoidalCategory ℛ
noncomputable local instance siteTensorLocalModelSymmetric :
    SymmetricCategory A := symmetricCategory ℛ

private theorem constant_tensor_iso :
    Nonempty ((Functor.postcompose₂.obj cB).obj (curriedTensor (ModuleCat.{u} B)) ≅
      (((Functor.whiskeringLeft₂ A).obj cB).obj cB).obj (curriedTensor A)) := by
  have := (realizationRingUnit_locallyBijective J B).1
  have := (realizationRingUnit_locallyBijective J B).2
  let P := siteConstantModulePresheafGeneral (C := C) B
  let S := PresheafOfModules.sheafification.{u} (R :=
    (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj ℛ)
    (realizationRingUnit J B)
  let : MonoidalCategory (PresheafOfModules.{u}
      ((Functor.const Cᵒᵖ).obj (RingCat.of B))) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of B) ⋙ forget₂ CommRingCat RingCat)))
  let p : tensor (ModuleCat.{u} B) ⋙ P ≅ P.prod P ⋙ tensor _ :=
    NatIso.ofComponents (fun MN ↦
      PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
        intro X Y f
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        rfl)) (by
          intro MN MN' fg
          ext X : 1
          apply ModuleCat.MonoidalCategory.tensor_ext
          intro x y
          rfl)
  obtain ⟨e, _⟩ := PresheafOfModules.exists_sheafificationTensorIso
    (O := (Functor.const Cᵒᵖ).obj (CommRingCat.of B))
    (R := ℛ) (realizationRingUnit J B)
  exact ⟨curried_tensor_iso cB (Functor.isoWhiskerRight p S ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (P.prod P) e.symm)⟩

private theorem constant_flat (M : ModuleCat.{u} B) [Module.Flat B M] :
    ObjectProperty.flat ((cB).obj M) := by
  let P : PresheafOfModules.{u}
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of B) ⋙ forget₂ CommRingCat RingCat) :=
    (siteConstantModulePresheafGeneral (C := C) B).obj M
  have hP : PreservesFiniteLimits (tensorRight P) := by
    constructor
    intro K hK hfin
    constructor
    intro D
    constructor
    intro c hc
    have : PreservesFiniteLimits (tensorRight M) := inferInstance
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦
      isLimitOfPreserves (tensorRight M)
        (isLimitOfPreserves (PresheafOfModules.evaluation _ X) hc))⟩
  have := (realizationRingUnit_locallyBijective J B).1
  have := (realizationRingUnit_locallyBijective J B).2
  have hflat := (PresheafOfModules.isFlat_sheafification_obj
      (O := (Functor.const Cᵒᵖ).obj (CommRingCat.of B))
      (R := ℛ) (realizationRingUnit J B) P hP).2
  exact ⟨(exactFunctor _ _).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight _).symm hflat, hflat⟩

private theorem constant_colimits : PreservesColimitsOfSize.{0, 0} (cB) := by
  let P := siteConstantModulePresheafGeneral (C := C) B
  have : PreservesColimitsOfSize.{0, 0} P := by
    constructor
    intro K _
    constructor
    intro D
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun _ ↦ hc)⟩
  have := (realizationRingUnit_locallyBijective J B).1
  have := (realizationRingUnit_locallyBijective J B).2
  change PreservesColimitsOfSize.{0, 0}
    (P ⋙ PresheafOfModules.sheafification.{u} (R :=
      (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj ℛ)
      (realizationRingUnit J B))
  infer_instance

private theorem restriction_colimits (U : C) :
    PreservesColimitsOfSize.{0, 0} (V U) := by
  let O := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj ℛ
  let S := PresheafOfModules.sheafification.{u} (𝟙 O.obj)
  let P := slicePresheafRestriction (J := J.over U) (Over.forget U) O
  let T := PresheafOfModules.sheafification.{u} (𝟙 (O.over U).obj)
  have : PreservesColimitsOfSize.{0, 0} P := by
    constructor
    intro K _
    constructor
    intro D
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦
      isColimitOfPreserves (PresheafOfModules.evaluation O.obj
        ((Over.forget U).op.obj X)) hc)⟩
  let e : S ⋙ (V U) ≅ P ⋙ T :=
    sliceSheafificationIso (J := J.over U) (Over.forget U) O
  have : PreservesColimitsOfSize.{0, 0} (S ⋙ (V U)) :=
    preservesColimits_of_natIso e.symm
  constructor
  intro K _
  constructor
  intro D
  let G := D ⋙ (SheafOfModules.forget O ⋙
    PresheafOfModules.restrictScalars (𝟙 O.obj))
  let eD : G ⋙ S ≅ D :=
    Functor.isoWhiskerLeft D
      (asIso (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 O.obj)).counit) ≪≫
      D.rightUnitor
  have : PreservesColimit (G ⋙ S) (V U) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves S (colimit.isColimit G))
      (isColimitOfPreserves (S ⋙ (V U)) (colimit.isColimit G))
  exact preservesColimit_of_iso_diagram (V U) eD

private theorem restriction_limits (U : C) : PreservesFiniteLimits (V U) := by
  constructor
  intro K hK hfin
  constructor
  intro D
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit D)
  apply isLimitOfReflects (SheafOfModules.forget _)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro X
  exact isLimitOfPreserves (SheafOfModules.evaluation _ ((Over.forget U).op.obj X))
    (limit.isLimit D)

@[irreducible]
private noncomputable def restriction_tensor_iso (U : C) :
    letI : MonoidalCategory (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj ℛ).over U)) :=
      monoidalCategory ((realizationRing J B).over U)
    (Functor.postcompose₂.obj (V U)).obj (curriedTensor A) ≅
      (((Functor.whiskeringLeft₂ _).obj (V U)).obj (V U)).obj
        (curriedTensor (SheafOfModules.{u} (((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj ℛ).over U))) := by
  letI : MonoidalCategory (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj ℛ).over U)) :=
      monoidalCategory ((realizationRing J B).over U)
  have hV {M N : A} (f : M ⟶ N) :
      (sliceCommModuleRestriction (J := J.over U) (Over.forget U) ℛ).map f =
        (V U).map f := by
    ext W x
    rfl
  let e : tensor A ⋙ (V U) ≅ (V U).prod (V U) ⋙ tensor _ :=
    NatIso.ofComponents (fun MN ↦
      sliceTensorIso (J := J.over U) (Over.forget U) ℛ MN.1 MN.2) (by
        intro MN MN' fg
        have h := sliceTensorIso_natural (J := J.over U) (Over.forget U) ℛ fg.1 fg.2
        rw [hV, hV, hV] at h
        exact h)
  exact curried_tensor_iso (V U) e

end Site

universe u
open CategoryTheory CategoryTheory.Limits

attribute [local irreducible] DerivedCategory.monoidalClosed

@[expose] public section

namespace SheafOfModules

variable {C : Type u} [Category.{u} C]

set_option quotPrecheck false in
set_option hygiene false in
local notation "𝓡(" J ", " B ")" => (sheafCompose J
  (forget₂ CommRingCat.{u} RingCat.{u})).obj
    ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B))
set_option quotPrecheck false in
set_option hygiene false in
local notation "cB(" J ", " B ")" => strictPerfectConstantPresheaf (C := C) B ⋙
  PresheafOfModules.sheafification.{u} (R := 𝓡(J, B)) (Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
    (forget₂ CommRingCat.{u} RingCat.{u}))

set_option linter.unusedVariables false in
set_option synthInstance.maxSize 256 in
/-- Local finite free models of the two relevant good truncations compute a fixed
degree of the original K-flat tensor. The comparison needs neither Noetherianity nor
local constancy hypotheses: the models are given.

Source: Stacks Project, Cohomology on Sites, Tag 094H, truncation and finite-free
computation; Tags 06YS, 06YQ, and Modules on Sites, Tag 0E8J.
(auxiliary; not a blueprint node).

Proof: Replace the factors by bounded-above flat complexes with their cohomological
upper bounds. K-flatness and the mapping-cone criterion show independence from the
given representatives. Restriction is exact, commutes with sheaf tensor and coproducts,
and preserves flatness, so it commutes with these derived tensor computations. For
cutoffs a = i-bQ and c = i-bP, the discarded lower truncation has upper cohomological
bound a-1, respectively c-1. Its tensor with the other factor has upper bound at most
i-1. The truncation triangle therefore gives an isomorphism on degree-i cohomology.
This also handles a cutoff larger than the upper bound: the corresponding object and
the relevant tensor cohomology are zero. Use the two given derived isomorphisms.
The constant realizations of E and F are termwise flat, since finite free modules
realize as finite sums of the ring sheaf; they are K-flat by their upper term bounds.
Their total tensor is the constant realization of the algebraic total tensor T:
the tensor-basis comparison in each bidegree commutes with both differentials and the
sign (-1)^p, and constant realization preserves coproducts. Taking cohomology on the slice
gives the asserted isomorphism. The comparison makes no assertion
about finite generation of the algebraic tensor or its cohomology. -/
theorem site_tensor_local_model_comparison
    (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    (P Q : CochainComplex (SheafOfModules.{u} (𝓡(J, B))) ℤ)
    (hP : P.IsKFlatTensor) (hQ : Q.IsKFlatTensor)
    (bP bQ : ℤ)
    (hPb : ∀ j : ℤ, bP < j → IsZero (P.homology j))
    (hQb : ∀ j : ℤ, bQ < j → IsZero (Q.homology j))
    (i : ℤ) (U : C) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} ((𝓡(J, B)).over U))
    ∀ (E F : CochainComplex (ModuleCat.{u} B) ℤ)
    (hEb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (E.X j))
    (hFb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (F.X j))
    (hE : ∀ j : ℤ, Module.Free B (E.X j) ∧ Module.Finite B (E.X j))
    (hF : ∀ j : ℤ, Module.Free B (F.X j) ∧ Module.Finite B (F.X j))
    (eE : Nonempty
      (DerivedCategory.Q.obj
          (((overFunctor.{u} (𝓡(J, B)) U).mapHomologicalComplex (.up ℤ)).obj
            (P.truncGE (i - bQ))) ≅
        DerivedCategory.Q.obj
          ((((cB(J, B)) ⋙ overFunctor.{u} (𝓡(J, B)) U).mapHomologicalComplex (.up ℤ)).obj E)))
    (eF : Nonempty
      (DerivedCategory.Q.obj
          (((overFunctor.{u} (𝓡(J, B)) U).mapHomologicalComplex (.up ℤ)).obj
            (Q.truncGE (i - bP))) ≅
        DerivedCategory.Q.obj
          ((((cB(J, B)) ⋙ overFunctor.{u} (𝓡(J, B)) U).mapHomologicalComplex (.up ℤ)).obj F))),
    let T := CochainComplex.mapBifunctor E F (MonoidalCategory.curriedTensor (ModuleCat B))
    Nonempty
      ((((overFunctor.{u} (𝓡(J, B)) U).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q
            (@MonoidalCategory.curriedTensor _ _ (monoidalCategory
              ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)))))).homology i ≅
        ((((cB(J, B)) ⋙ overFunctor.{u} (𝓡(J, B)) U).mapHomologicalComplex
          (.up ℤ)).obj T).homology i) := by
  classical
  let R := realizationRing J B
  let A := realizationModules J B
  let D := SheafOfModules.{u} ((𝓡(J, B)).over U)
  let : HasDerivedCategory.{u + 1} D := HasDerivedCategory.standard D
  intro E F hEb hFb hE hF eE eF
  dsimp only
  let V : A ⥤ D := overFunctor.{u} (𝓡(J, B)) U
  let W := V.mapHomologicalComplex (.up ℤ)
  let K := commutativeSiteConstantModuleFunctor J B ⋙ V
  let : HasDerivedCategory.{u + 1} A := HasDerivedCategory.standard A
  let : MonoidalCategory A := monoidalCategory R
  let : SymmetricCategory A := symmetricCategory R
  let : MonoidalPreadditive A := (tensorClosed R).1.some
  let : MonoidalClosed A := (tensorClosed R).2.1.some
  have : IsGrothendieckAbelian.{u} A := isGrothendieckAbelian _
  have : Abelian.HasFunctorialFlatResolution A := hasFunctorialFlatResolution_kfi R
  let : MonoidalCategory D := monoidalCategory (R.over U)
  let : SymmetricCategory D := symmetricCategory (R.over U)
  let : MonoidalPreadditive D := (tensorClosed (R.over U)).1.some
  let : MonoidalClosed D := (tensorClosed (R.over U)).2.1.some
  have : IsGrothendieckAbelian.{u} D := isGrothendieckAbelian _
  have : Abelian.HasFunctorialFlatResolution D :=
    hasFunctorialFlatResolution_kfi (R.over U)
  have : V.Additive := ⟨by intros; ext X x; rfl⟩
  have : PreservesFiniteLimits V := restriction_limits J B U
  have : PreservesColimitsOfSize.{0, 0} V := restriction_colimits J B U
  have flatV (M : A) (hM : ObjectProperty.flat M) : ObjectProperty.flat (V.obj M) := by
    have : PreservesFiniteLimits (tensorRight (V.obj M)) :=
      isFlat_over_preservesFiniteLimits M U hM.2 _ rfl
    exact (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _).symm)
  have hbP : P.IsLE bP := by
    rw [CochainComplex.isLE_iff]
    intro j hj
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hPb j hj
  have hbQ : Q.IsLE bQ := by
    rw [CochainComplex.isLE_iff]
    intro j hj
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hQb j hj
  have bound (L : CochainComplex A ℤ) (b : ℤ) [L.IsLE b] :
      (DerivedCategory.Q.obj (W.obj L)).IsLE b := by
    let e : V.mapDerivedCategory.obj (DerivedCategory.Q.obj L) ≅
        DerivedCategory.Q.obj (W.obj L) := V.mapDerivedCategoryFactors.app L
    have : (V.mapDerivedCategory.obj (DerivedCategory.Q.obj L)).IsLE b :=
      V.isLE_mapDerivedCategory_obj (DerivedCategory.Q.obj L) b
    exact DerivedCategory.TStructure.t.isLE_of_iso e b
  have := bound Q bQ
  obtain ⟨e0⟩ := tensor_image_compare (D := D) V flatV (restriction_tensor_iso J B U)
    P Q bP bQ (kflat_of_acyclic P hP) (kflat_of_acyclic Q hQ)
  obtain ⟨e1⟩ := tensor_truncGE_image_left V P (DerivedCategory.Q.obj (W.obj Q)) bQ i
  have hbPT : (P.truncGE (i - bQ)).IsLE bP := by
    rw [CochainComplex.isLE_iff]
    intro j hj
    by_cases ha : i - bQ ≤ j
    · have := P.quasiIsoAt_πTruncGE (i - bQ) j ha
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact (asIso (HomologicalComplex.homologyMap (P.πTruncGE (i - bQ)) j)).isZero_iff.1
        (hPb j hj)
    · exact (P.truncGE (i - bQ)).exactAt_of_isGE (i - bQ) j (by omega)
  have := bound (P.truncGE (i - bQ)) bP
  obtain ⟨e2⟩ := tensor_truncGE_image_right V Q
    (DerivedCategory.Q.obj (W.obj (P.truncGE (i - bQ)))) bP i
  clear hFb hF
  obtain ⟨r, hr⟩ := hEb
  have : E.IsStrictlyLE r := (CochainComplex.isStrictlyLE_iff E r).2 hr
  let CE := (K.mapHomologicalComplex (.up ℤ)).obj E
  let CF := (K.mapHomologicalComplex (.up ℤ)).obj F
  have flatCE (n : ℤ) : ObjectProperty.flat (CE.X n) := by
    let : Module.Free B (E.X n) := (hE n).1
    exact flatV _ (constant_flat J B (E.X n))
  have hkCE := CochainComplex.kFlat_of_isStrictlyLE_of_flat CE r flatCE
  change Nonempty (DerivedCategory.Q.obj (W.obj (P.truncGE (i - bQ))) ≅
    DerivedCategory.Q.obj CE) at eE
  change Nonempty (DerivedCategory.Q.obj (W.obj (Q.truncGE (i - bP))) ≅
    DerivedCategory.Q.obj CF) at eF
  have : PreservesColimitsOfSize.{0, 0} (commutativeSiteConstantModuleFunctor J B) :=
    constant_colimits J B
  obtain ⟨τ⟩ := constant_tensor_iso J B
  let ec := asIso (HomologicalComplex.mapBifunctorComparison τ.hom (.up ℤ) E F)
  let er := asIso (HomologicalComplex.mapBifunctorComparison
    (restriction_tensor_iso J B U).hom (.up ℤ)
      (((commutativeSiteConstantModuleFunctor J B).mapHomologicalComplex (.up ℤ)).obj E)
      (((commutativeSiteConstantModuleFunctor J B).mapHomologicalComplex (.up ℤ)).obj F))
  let et := W.mapIso ec ≪≫ er
  let H := DerivedCategory.homologyFunctor D i
  let ei := H.mapIso e0 ≪≫ e1 ≪≫ e2 ≪≫
    H.mapIso (tensorIso eE.some eF.some ≪≫
      DerivedCategory.QObjTensorQObjIsoOfKFlatLeft CE CF hkCE ≪≫
      DerivedCategory.Q.mapIso et.symm)
  exact ⟨(DerivedCategory.homologyFunctorFactors D i).symm.app _ ≪≫ ei ≪≫
    (DerivedCategory.homologyFunctorFactors D i).app _⟩

end SheafOfModules
