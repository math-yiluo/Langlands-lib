/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import WeilConjectures.CategoryTheory.RingedSiteLocalization
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import WeilConjectures.RingTheory.TwoLocalizationExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # The binary localization Cech sequence

Source: Stacks Project, Tags 00EJ and 0998.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

namespace CategoryTheory

private noncomputable def fractionStage
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U)) (n : ℕ) :
    PresheafOfModules.unit
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U).obj ⟶
      ringedSectionLocalizationPresheaf (R.over U) (ringedSliceSection R U f) := by
  let s := ringedSliceSection R U f
  let F := ringedSectionLocalizationPresheaf (R.over U) s
  refine F.unitHomEquiv.symm (PresheafOfModules.sectionsMk
    (fun X ↦ IsLocalization.mk' (R := (R.over U).obj.obj X)
      (M := Submonoid.powers (show (R.over U).obj.obj X from s.val X))
      (ringedSectionLocalizationCarrier (R.over U) s X)
      1 ⟨(show (R.over U).obj.obj X from s.val X) ^ n, ⟨n, rfl⟩⟩) ?_)
  intro X Y a
  change ringedSectionLocalizationMap (R.over U) s a
      (IsLocalization.mk' (R := (R.over U).obj.obj X)
        (M := Submonoid.powers (show (R.over U).obj.obj X from s.val X))
        _ 1 ⟨_, ⟨n, rfl⟩⟩) = _
  simp only [ringedSectionLocalizationMap, IsLocalization.Away.lift]
  rw [IsLocalization.lift_mk'_spec]
  have hs : (R.over U).obj.map a (show (R.over U).obj.obj X from s.val X) =
      (show (R.over U).obj.obj Y from s.val Y) := s.property a
  simp only [RingHom.comp_apply, map_one, map_pow, hs]
  simpa only [map_one, map_pow] using (IsLocalization.mk'_spec'
    (ringedSectionLocalizationCarrier (R.over U) s Y) 1
    (⟨_, ⟨n, rfl⟩⟩ : Submonoid.powers
      (show (R.over U).obj.obj Y from s.val Y))).symm

private noncomputable def localization_fraction_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U)) :
    ringedSiteSectionLocalization
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U f ≅
      ringedSectionLocalization (R.over U) (ringedSliceSection R U f) := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let t : End (SheafOfModules.unit (O.over U)) :=
    .of ((SheafOfModules.unit (O.over U)).unitHomEquiv.symm
      (PresheafOfModules.sectionsMk (fun X ↦ O.obj.map X.unop.hom.op f)
        (fun {X Y} a ↦ ringedSiteSectionLocalization_compatible O U f X Y a)))
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ SheafOfModules.unit (O.over U))
    (fun _ ↦ (t).asHom)
  let Dp := D ⋙ SheafOfModules.forget (O.over U)
  let s := ringedSliceSection R U f
  let F := ringedSectionLocalizationPresheaf (R.over U) s
  have h (n : ℕ) : Dp.map (homOfLE (Nat.le_add_right n 1)) ≫ fractionStage R U f (n + 1) =
      fractionStage R U f n := by
    simp only [Dp, D, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (R.over U).obj.obj X at x
    change (x * (show (R.over U).obj.obj X from s.val X)) •
        IsLocalization.mk' (R := (R.over U).obj.obj X)
          (M := Submonoid.powers (show (R.over U).obj.obj X from s.val X))
          (ringedSectionLocalizationCarrier (R.over U) s X) 1 ⟨_, ⟨n + 1, rfl⟩⟩ =
      x • IsLocalization.mk' (R := (R.over U).obj.obj X)
          (M := Submonoid.powers (show (R.over U).obj.obj X from s.val X))
          (ringedSectionLocalizationCarrier (R.over U) s X) 1 ⟨_, ⟨n, rfl⟩⟩
    simp only [IsLocalization.smul_mk', mul_one]
    convert! IsLocalization.mk'_cancel x
      (⟨_, ⟨n, rfl⟩⟩ : Submonoid.powers (show (R.over U).obj.obj X from s.val X))
      (⟨_, ⟨1, pow_one _⟩⟩ : Submonoid.powers (show (R.over U).obj.obj X from s.val X))
      using 1
    simp only [pow_succ]
    congr 1
  let c : Cocone Dp :=
    { pt := F
      ι := NatTrans.ofSequence (fractionStage R U f) h }
  have hc : IsColimit c := by
    apply PresheafOfModules.evaluationJointlyReflectsColimits
    intro X
    let A : CommRingCat.{u} := (R.over U).obj.obj X
    let a : A := s.val X
    let D₀ : ℕ ⥤ ModuleCat.{u} A :=
      Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of A A)
        (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul A A a))
    have ht (n : ℕ) :
        (Dp ⋙ PresheafOfModules.evaluation (O.over U).obj X).map
            (homOfLE (Nat.le_add_right n 1)) ≫ 𝟙 (ModuleCat.of A A) =
          𝟙 (ModuleCat.of A A) ≫ D₀.map (homOfLE (Nat.le_add_right n 1)) := by
      simp only [Dp, D, D₀, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
        Category.id_comp]
      apply ConcreteCategory.hom_ext
      intro x
      change A at x
      change x * a = a * x
      exact mul_comm _ _
    let α : Dp ⋙ PresheafOfModules.evaluation (O.over U).obj X ⟶ D₀ :=
      NatTrans.ofSequence (fun _ ↦ 𝟙 (ModuleCat.of A A)) ht
    let e : Dp ⋙ PresheafOfModules.evaluation (O.over U).obj X ≅ D₀ :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun b ↦ α.naturality b)
    let κ := Classical.choose (ModuleCat.localization_away_colimit a A)
    have hκ := Classical.choose_spec (ModuleCat.localization_away_colimit a A)
    let eκ : colimit D₀ ≅ F.obj X := κ.toModuleIso
    refine IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext
      (HasColimit.isoOfNatIso e ≪≫ eκ) ?_)
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((colimit.ι _ n ≫ (HasColimit.isoOfNatIso e).hom ≫ eκ.hom) x) = _
    rw [HasColimit.ι_isoOfNatIso_hom_assoc]
    change κ ((colimit.ι D₀ n) x) = _
    rw [hκ]
    change A at x
    change LocalizedModule.mk x (⟨a ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers a) =
      x • IsLocalization.mk' (M := Submonoid.powers a) (Localization.Away a) 1 ⟨a ^ n, ⟨n, rfl⟩⟩
    rw [IsLocalization.smul_mk', mul_one]
    exact Localization.mk_eq_mk'_apply _ _
  let sh := PresheafOfModules.sheafification (𝟙 (O.over U).obj)
  let eD : Dp ⋙ sh ≅ D := Functor.isoWhiskerLeft D
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (O.over U).obj)).counit)
  exact HasColimit.isoOfNatIso eD.symm ≪≫ (preservesColimitIso sh Dp).symm ≪≫
    sh.mapIso ((colimit.isColimit Dp).coconePointUniqueUpToIso hc)

private theorem localization_over_product
    (A : Type u) [CommRing A] (h f : A) :
    let H := Localization.Away h
    let S := Localization.Away (h * f)
    let φ : H →+* S := IsLocalization.Away.lift h
      (IsLocalization.Away.isUnit_of_dvd (h * f) (dvd_mul_right h f))
    letI : Algebra H S := φ.toAlgebra
    IsLocalization.Away (algebraMap A H f) S := by
  let H := Localization.Away h
  let S := Localization.Away (h * f)
  let φ : H →+* S := IsLocalization.Away.lift h
    (IsLocalization.Away.isUnit_of_dvd (h * f) (dvd_mul_right h f))
  let : Algebra H S := φ.toAlgebra
  have hφ (a : A) : φ (algebraMap A H a) = algebraMap A S a :=
    IsLocalization.Away.lift_eq _ _ _
  let : IsScalarTower A H S := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (hφ a).symm)
  let T := Localization.Away (algebraMap A H f)
  let e : T ≃ₐ[A] S := IsLocalization.algEquiv (Submonoid.powers (h * f)) T S
  have he : e.toRingHom.comp (algebraMap H T) = φ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers h)
    ext a
    change e (algebraMap H T (algebraMap A H a)) = φ (algebraMap A H a)
    rw [← IsScalarTower.algebraMap_apply A H T, e.commutes, hφ]
  let e' : T ≃ₐ[H] S :=
    { e.toRingEquiv with commutes' := fun a ↦ RingHom.congr_fun he a }
  exact IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (algebraMap A H f)) e'

private theorem localization_over_factor
    (A : Type u) [CommRing A] (h f k : A) (hk : k = h * f) (hd : h ∣ k) :
    let H := Localization.Away h
    let S := Localization.Away k
    let φ : H →+* S := IsLocalization.Away.lift h
      (IsLocalization.Away.isUnit_of_dvd k hd)
    letI : Algebra H S := φ.toAlgebra
    IsLocalization.Away (algebraMap A H f) S := by
  subst k
  exact localization_over_product A h f

private noncomputable def fractionRingMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (s t : (R.obj ⋙ forget CommRingCat).sections)
    (hd : ∀ X, (show R.obj.obj X from s.val X) ∣ (show R.obj.obj X from t.val X))
    (X : Cᵒᵖ) :
    ringedSectionLocalizationCarrier R s X →+* ringedSectionLocalizationCarrier R t X :=
  IsLocalization.Away.lift (show R.obj.obj X from s.val X)
    (IsLocalization.Away.isUnit_of_dvd (show R.obj.obj X from t.val X) (hd X))

private theorem fractionRingMap_algebraMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (s t : (R.obj ⋙ forget CommRingCat).sections)
    (hd : ∀ X, (show R.obj.obj X from s.val X) ∣ (show R.obj.obj X from t.val X))
    (X : Cᵒᵖ) (a : R.obj.obj X) :
    fractionRingMap R s t hd X (algebraMap (R.obj.obj X) _ a) =
      algebraMap (R.obj.obj X) _ a :=
  IsLocalization.Away.lift_eq _ _ _

private noncomputable def fractionMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (s t : (R.obj ⋙ forget CommRingCat).sections)
    (hd : ∀ X, (show R.obj.obj X from s.val X) ∣ (show R.obj.obj X from t.val X)) :
    ringedSectionLocalizationPresheaf R s ⟶ ringedSectionLocalizationPresheaf R t where
  app X := ModuleCat.ofHom
    { toFun := fractionRingMap R s t hd X
      map_add' := map_add _
      map_smul' := fun a x ↦ by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul,
          fractionRingMap_algebraMap] }
  naturality {X Y} a := by
    have h : (ringedSectionLocalizationMap R t a).comp (fractionRingMap R s t hd X) =
        (fractionRingMap R s t hd Y).comp (ringedSectionLocalizationMap R s a) := by
      apply IsLocalization.ringHom_ext
        (Submonoid.powers (show R.obj.obj X from s.val X))
      ext r
      simp [fractionRingMap_algebraMap, ringedSectionLocalizationMap]
    apply ConcreteCategory.hom_ext
    intro x
    exact (RingHom.congr_fun h x).symm

private noncomputable def presheafPair
    {C : Type u} [SmallCategory C] (O : Cᵒᵖ ⥤ RingCat.{u})
    (F G : PresheafOfModules.{u} O) : PresheafOfModules.{u} O where
  obj X := ModuleCat.of (O.obj X) (F.obj X × G.obj X)
  map {X Y} a := ModuleCat.ofHom
    (X := ModuleCat.of (O.obj X) (F.obj X × G.obj X))
    (Y := (ModuleCat.restrictScalars (O.map a).hom).obj
      (ModuleCat.of (O.obj Y) (F.obj Y × G.obj Y)))
    { toFun := fun x ↦ (F.map a x.1, G.map a x.2)
      map_add' := fun x y ↦ Prod.ext (map_add _ _ _) (map_add _ _ _)
      map_smul' := fun r x ↦ by
        change (F.map a (r • x.1), G.map a (r • x.2)) =
          ((O.map a).hom r • F.map a x.1, (O.map a).hom r • G.map a x.2)
        exact Prod.ext (F.map_smul a r x.1) (G.map_smul a r x.2) }
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · change F.map (𝟙 X) x.1 = x.1
      simpa only [ModuleCat.restrictScalarsId', NatIso.ofComponents_inv_app,
        ModuleCat.restrictScalarsId'App_inv_apply] using
        ConcreteCategory.congr_hom (F.map_id X) x.1
    · change G.map (𝟙 X) x.2 = x.2
      simpa only [ModuleCat.restrictScalarsId', NatIso.ofComponents_inv_app,
        ModuleCat.restrictScalarsId'App_inv_apply] using
        ConcreteCategory.congr_hom (G.map_id X) x.2
  map_comp a b := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext (F.map_comp_apply a b x.1) (G.map_comp_apply a b x.2)

private noncomputable def presheafPairFst
    {C : Type u} [SmallCategory C] (O : Cᵒᵖ ⥤ RingCat.{u})
    (F G : PresheafOfModules.{u} O) : presheafPair O F G ⟶ F where
  app X := ModuleCat.ofHom (LinearMap.fst (O.obj X) (F.obj X) (G.obj X))
  naturality _ := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

private noncomputable def presheafPairSnd
    {C : Type u} [SmallCategory C] (O : Cᵒᵖ ⥤ RingCat.{u})
    (F G : PresheafOfModules.{u} O) : presheafPair O F G ⟶ G where
  app X := ModuleCat.ofHom (LinearMap.snd (O.obj X) (F.obj X) (G.obj X))
  naturality _ := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

private noncomputable def presheafPairIso
    {C : Type u} [SmallCategory C] (O : Cᵒᵖ ⥤ RingCat.{u})
    (F G : PresheafOfModules.{u} O) : presheafPair O F G ≅ F ⊞ G := by
  let c := BinaryFan.mk (presheafPairFst O F G) (presheafPairSnd O F G)
  have hc : IsLimit c := by
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro X
    refine (BinaryFan.isLimitMapConeEquiv
      (F := PresheafOfModules.evaluation O X) (s := c)).symm ?_
    apply IsLimit.ofIsoLimit (ModuleCat.binaryProductLimitCone (F.obj X) (G.obj X)).isLimit
    exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩ <;> rfl)
  exact hc.conePointUniqueUpToIso (BinaryBiproduct.isLimit F G)

private theorem localization_presheaf_cech
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U : C) (f g : R.obj.obj (op U)) :
    let O := (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U).obj
    let L := fun a ↦ ringedSectionLocalizationPresheaf (R.over U) (ringedSliceSection R U a)
    ∃ (i : L (f + g) ⟶ presheafPair O (L ((f + g) * f)) (L ((f + g) * g)))
      (p : presheafPair O (L ((f + g) * f)) (L ((f + g) * g)) ⟶
        L (((f + g) * f) * g)) (hp : i ≫ p = 0),
      (ShortComplex.mk i p hp).ShortExact := by
  let O := (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U).obj
  let s := ringedSliceSection R U
  let L := fun a ↦ ringedSectionLocalizationPresheaf (R.over U) (s a)
  let h := f + g
  have hd (a b : R.obj.obj (op U)) (X : (Over U)ᵒᵖ) :
      (show (R.over U).obj.obj X from (s a).val X) ∣
        (show (R.over U).obj.obj X from (s (a * b)).val X) := by
    change R.obj.map X.unop.hom.op a ∣ R.obj.map X.unop.hom.op (a * b)
    rw [map_mul]
    exact dvd_mul_right _ _
  have hd₄ (X : (Over U)ᵒᵖ) :
      (show (R.over U).obj.obj X from (s (h * g)).val X) ∣
        (show (R.over U).obj.obj X from (s ((h * f) * g)).val X) := by
    refine ⟨R.obj.map X.unop.hom.op f, ?_⟩
    change R.obj.map X.unop.hom.op ((h * f) * g) =
      R.obj.map X.unop.hom.op (h * g) * R.obj.map X.unop.hom.op f
    simp only [map_mul]
    ring
  have hd₀ (X : (Over U)ᵒᵖ) :
      (show (R.over U).obj.obj X from (s h).val X) ∣
        (show (R.over U).obj.obj X from (s ((h * f) * g)).val X) := by
    refine ⟨R.obj.map X.unop.hom.op (f * g), ?_⟩
    change R.obj.map X.unop.hom.op ((h * f) * g) =
      R.obj.map X.unop.hom.op h * R.obj.map X.unop.hom.op (f * g)
    simp only [map_mul, mul_assoc]
  let m₁ := fractionMap (R.over U) (s h) (s (h * f)) (hd h f)
  let m₂ := fractionMap (R.over U) (s h) (s (h * g)) (hd h g)
  let n₁ := fractionMap (R.over U) (s (h * f)) (s ((h * f) * g)) (hd (h * f) g)
  let n₂ := fractionMap (R.over U) (s (h * g)) (s ((h * f) * g)) hd₄
  let i : L h ⟶ presheafPair O (L (h * f)) (L (h * g)) :=
    { app X := ModuleCat.ofHom ((m₁.app X).hom.prod (m₂.app X).hom)
      naturality a := by
        apply ConcreteCategory.hom_ext
        intro x
        exact Prod.ext (ConcreteCategory.congr_hom (m₁.naturality a) x)
          (ConcreteCategory.congr_hom (m₂.naturality a) x) }
  let p : presheafPair O (L (h * f)) (L (h * g)) ⟶ L ((h * f) * g) :=
    presheafPairFst O _ _ ≫ n₁ - presheafPairSnd O _ _ ≫ n₂
  have hp : i ≫ p = 0 := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ConcreteCategory.hom_ext
    intro x
    have he : (fractionRingMap (R.over U) (s (h * f)) (s ((h * f) * g))
          (hd (h * f) g) X).comp
          (fractionRingMap (R.over U) (s h) (s (h * f)) (hd h f) X) =
        (fractionRingMap (R.over U) (s (h * g)) (s ((h * f) * g)) hd₄ X).comp
          (fractionRingMap (R.over U) (s h) (s (h * g)) (hd h g) X) := by
      apply IsLocalization.ringHom_ext
        (Submonoid.powers (show (R.over U).obj.obj X from (s h).val X))
      ext a
      simp only [RingHom.comp_apply, fractionRingMap_algebraMap]
    exact sub_eq_zero.mpr (RingHom.congr_fun he x)
  have hpoint (X : (Over U)ᵒᵖ) :
      Function.Injective (i.app X) ∧ Function.Exact (i.app X) (p.app X) ∧
        Function.Surjective (p.app X) := by
    let A : CommRingCat.{u} := (R.over U).obj.obj X
    let a : A := (s f).val X
    let b : A := (s g).val X
    let c : A := (s h).val X
    let H := ringedSectionLocalizationCarrier (R.over U) (s h) X
    let S := ringedSectionLocalizationCarrier (R.over U) (s (h * f)) X
    let T := ringedSectionLocalizationCarrier (R.over U) (s (h * g)) X
    let P := ringedSectionLocalizationCarrier (R.over U) (s ((h * f) * g)) X
    let : Algebra H S := (fractionRingMap (R.over U) (s h) (s (h * f)) (hd h f) X).toAlgebra
    let : Algebra H T := (fractionRingMap (R.over U) (s h) (s (h * g)) (hd h g) X).toAlgebra
    let : Algebra H P := (fractionRingMap (R.over U) (s h) (s ((h * f) * g)) hd₀ X).toAlgebra
    have hS : IsLocalization.Away (algebraMap A H a) S := by
      apply localization_over_factor A c a
        (show A from (s (h * f)).val X) _ (hd h f X)
      change R.obj.map X.unop.hom.op (h * f) =
        R.obj.map X.unop.hom.op h * R.obj.map X.unop.hom.op f
      exact map_mul _ _ _
    have hT : IsLocalization.Away (algebraMap A H b) T := by
      apply localization_over_factor A c b
        (show A from (s (h * g)).val X) _ (hd h g X)
      exact map_mul _ _ _
    have hP : IsLocalization.Away (algebraMap A H a * algebraMap A H b) P := by
      rw [← map_mul]
      apply localization_over_factor A c (a * b)
        (show A from (s ((h * f) * g)).val X) _ (hd₀ X)
      change R.obj.map X.unop.hom.op ((h * f) * g) =
        R.obj.map X.unop.hom.op h *
          (R.obj.map X.unop.hom.op f * R.obj.map X.unop.hom.op g)
      simp only [map_mul, mul_assoc]
    let : IsScalarTower A H S := IsScalarTower.of_algebraMap_eq fun r ↦
      (fractionRingMap_algebraMap (R.over U) (s h) (s (h * f)) (hd h f) X r).symm
    let : IsScalarTower A H T := IsScalarTower.of_algebraMap_eq fun r ↦
      (fractionRingMap_algebraMap (R.over U) (s h) (s (h * g)) (hd h g) X r).symm
    let : IsScalarTower A H P := IsScalarTower.of_algebraMap_eq fun r ↦
      (fractionRingMap_algebraMap (R.over U) (s h) (s ((h * f) * g)) hd₀ X r).symm
    have hu : IsUnit (algebraMap A H a + algebraMap A H b) := by
      rw [← map_add]
      have hc : c = a + b := by
        change R.obj.map X.unop.hom.op (f + g) =
          R.obj.map X.unop.hom.op f + R.obj.map X.unop.hom.op g
        exact map_add _ _ _
      rw [← hc]
      exact IsLocalization.Away.algebraMap_isUnit c
    obtain ⟨u, hu⟩ := hu
    have hc : IsCoprime (algebraMap A H a) (algebraMap A H b) := by
      refine ⟨↑u⁻¹, ↑u⁻¹, ?_⟩
      rw [← mul_add, ← hu]
      exact Units.inv_mul u
    let F := IsLocalization.Away.awayToAwayRight
      (S := S) (P := P) (algebraMap A H a) (algebraMap A H b)
    let G := IsLocalization.Away.awayToAwayLeft
      (S := T) (P := P) (algebraMap A H b) (algebraMap A H a)
    have hF : F = fractionRingMap (R.over U) (s (h * f))
        (s ((h * f) * g)) (hd (h * f) g) X := by
      apply IsLocalization.ringHom_ext
        (Submonoid.powers (show A from (s (h * f)).val X))
      ext r
      change F (algebraMap A S r) = _
      rw [IsScalarTower.algebraMap_apply A H S]
      rw [IsLocalization.Away.awayToAwayRight_eq]
      rw [← IsScalarTower.algebraMap_apply A H P]
      exact (fractionRingMap_algebraMap (R.over U) (s (h * f))
        (s ((h * f) * g)) (hd (h * f) g) X r).symm
    have hG : G = fractionRingMap (R.over U) (s (h * g))
        (s ((h * f) * g)) hd₄ X := by
      apply IsLocalization.ringHom_ext
        (Submonoid.powers (show A from (s (h * g)).val X))
      ext r
      change G (algebraMap A T r) = _
      rw [IsScalarTower.algebraMap_apply A H T]
      rw [IsLocalization.Away.awayToAwayLeft_eq]
      rw [← IsScalarTower.algebraMap_apply A H P]
      exact (fractionRingMap_algebraMap (R.over U) (s (h * g))
        (s ((h * f) * g)) hd₄ X r).symm
    have he := localization_two_exact (algebraMap A H a) (algebraMap A H b) hc S T P
    change Function.Injective (fun x : H ↦ (algebraMap H S x, algebraMap H T x)) ∧
      Function.Exact (fun x : H ↦ (algebraMap H S x, algebraMap H T x))
        (fun x : S × T ↦ F x.1 - G x.2) ∧
      Function.Surjective (fun x : S × T ↦ F x.1 - G x.2) at he
    rw [hF, hG] at he
    exact he
  let S := ShortComplex.mk i p hp
  let : Mono i := PresheafOfModules.mono_of_injective fun {X} ↦ (hpoint X).1
  let : Epi p := PresheafOfModules.epi_of_surjective fun {X} ↦ (hpoint X).2.2
  have hex : S.Exact := by
    rw [S.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    apply PresheafOfModules.hom_ext
    intro X
    let E := PresheafOfModules.evaluation O X
    have hX : (S.map E).Exact :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (hpoint X).2.1
    have hz : IsZero (E.obj S.homology) :=
      ((S.map E).exact_iff_isZero_homology.mp hX).of_iso
        (S.mapHomologyIso E).symm
    change 𝟙 (E.obj S.homology) = 0
    exact hz.eq_of_src _ _
  exact ⟨i, p, hp, ⟨hex⟩⟩

/-- The binary Cech row for localization at f+g is short exact.

Proof: Evaluate the fraction presheaves at V→U and set A=O(V)[1/(f+g)].
The elements f and g generate the unit ideal of A. Standard-covering gluing
(Tag 00EJ) gives injectivity of the diagonal A→A[1/f]⊕A[1/g] and identifies
its image with the kernel of the difference map to A[1/(fg)]. For surjectivity,
write z/(fg)^n, with n positive. The equality (f/(f+g)+g/(f+g))^(2*n-1)=1
provides u*f^n+v*g^n=1. The pair (v*z/f^n,-u*z/g^n) maps to the given
fraction. All maps commute with restriction. Exact module sheafification
preserves the row. The sequential colimit defining section localization is
canonically the sheafified fraction presheaf: send the nth copy of O to
x↦x/f^n and use the localization universal property for its inverse.
Iterated localizations identify with localization at the product. The maps
transported along these comparisons give i and p. No nonzero hypothesis
is used, so the argument includes f=0, g=0 and f+g=0.

Source: Stacks Project, algebra.tex, Tag 00EJ; algebraization.tex, Tag 0998.
(auxiliary; not a blueprint node). -/
theorem ringedSite_localization_cech
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U : C) (f g : R.obj.obj (op U)) :
    let O : Sheaf J RingCat.{u} :=
      (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    let L : O.obj.obj (op U) → SheafOfModules.{u} (O.over U) :=
      fun a ↦ ringedSiteSectionLocalization O U a
    ∃ (i : L (f + g) ⟶ L ((f + g) * f) ⊞ L ((f + g) * g))
      (p : L ((f + g) * f) ⊞ L ((f + g) * g) ⟶ L (((f + g) * f) * g))
      (hp : i ≫ p = 0), (ShortComplex.mk i p hp).ShortExact := by
  let O : Sheaf J RingCat.{u} :=
    (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let sh := PresheafOfModules.sheafification (𝟙 (O.over U).obj)
  let L := fun a ↦ ringedSectionLocalizationPresheaf (R.over U) (ringedSliceSection R U a)
  obtain ⟨i, p, hp, he⟩ := localization_presheaf_cech J R U f g
  let S := ShortComplex.mk i p hp
  have hs : (S.map sh).ShortExact := he.map_of_exact sh
  let e₁ : sh.obj (L (f + g)) ≅ ringedSiteSectionLocalization O U (f + g) :=
    (localization_fraction_iso R U (f + g)).symm
  let : PreservesBinaryBiproducts sh :=
    preservesBinaryBiproducts_of_preservesBinaryProducts sh
  let e₂ : sh.obj (presheafPair (O.over U).obj (L ((f + g) * f))
      (L ((f + g) * g))) ≅
      ringedSiteSectionLocalization O U ((f + g) * f) ⊞
        ringedSiteSectionLocalization O U ((f + g) * g) :=
    sh.mapIso (presheafPairIso _ _ _) ≪≫
      sh.mapBiprod _ _ ≪≫ biprod.mapIso
        (localization_fraction_iso R U ((f + g) * f)).symm
        (localization_fraction_iso R U ((f + g) * g)).symm
  let e₃ : sh.obj (L (((f + g) * f) * g)) ≅
      ringedSiteSectionLocalization O U (((f + g) * f) * g) :=
    (localization_fraction_iso R U (((f + g) * f) * g)).symm
  let i' := e₁.inv ≫ sh.map i ≫ e₂.hom
  let p' := e₂.inv ≫ sh.map p ≫ e₃.hom
  have hp' : i' ≫ p' = 0 := by
    simp only [i', p', Category.assoc, Iso.hom_inv_id_assoc, ← sh.map_comp_assoc,
      hp, sh.map_zero, zero_comp, comp_zero]
  let T := ShortComplex.mk i' p' hp'
  let e : S.map sh ≅ T := ShortComplex.isoMk e₁ e₂ e₃
    (by simp [T, i', S]) (by simp [T, p', S])
  exact ⟨i', p', hp', ShortComplex.shortExact_of_iso e hs⟩

end CategoryTheory
