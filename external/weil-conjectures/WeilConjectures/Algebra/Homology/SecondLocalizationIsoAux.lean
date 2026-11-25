/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.SecondLocalizationMap
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import all WeilConjectures.Algebra.Homology.FirstLocalizationMap

/-! Auxiliary interfaces for the second localization isomorphism.
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-iso-aux)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R A B Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra B Bp] [Algebra R Bp]
  [tRB : IsScalarTower R B Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[R] Bp) D]
  [Algebra A D] [Algebra B D] [Algebra Bp D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[R] Bp) D]
  [tBpD : IsScalarTower Bp (A ⊗[R] Bp) D]
  [tBBpD : IsScalarTower B Bp D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

omit [Algebra A D] [Algebra B D] [Algebra Bp D] tAD tBD tApD tBpD tBBpD in
private theorem secondLocalizationDerivedMap_app_isIso
    (hflat : (algebraMap B Bp).Flat)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (V : CochainComplex (ModuleCat.{u} R) ℤ) :
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
    IsIso ((secondLocalizationDerivedMap R A B Bp D hflat Q L K).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj V))) := by
  classical
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  have (N : ModuleCat.{u} R) : CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      ((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R)).flip.obj N) :=
    inferInstanceAs (CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      (CategoryTheory.MonoidalCategory.tensorRight N))
  have : CategoryTheory.HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
    CategoryTheory.HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (AsSmall.equiv (C := ℤ)).symm
  let Λ := (Classical.choice (inferInstance :
    CategoryTheory.Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R))).reduced
  let P := Λ.resolutionFunctor.obj V
  let s := Λ.resolutionNatTrans.app V
  have hs : QuasiIso s := inferInstance
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  have hk := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le V
  have hP : ∀ N : CochainComplex (ModuleCat.{u} R) ℤ, N.Acyclic →
      (CochainComplex.mapBifunctor N P
        (CategoryTheory.MonoidalCategory.curriedTensor _)).Acyclic := by
    intro N hN
    have hk' := (HomotopyCategory.kFlat_quotient_obj_iff P).2 hk
    have hc := ((HomotopyCategory.kFlat_iff_preserves_acyclic _).1 hk'
      (q.obj N) ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic N).2 hN)).2
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 hc
  let := ModuleCat.scalarExtensionCounit_isIso_of_kFlat (algebraMap R B) P hP
    L.derived L.counit L.universal
  let := ModuleCat.scalarExtensionCounit_isIso_of_kFlat (algebraMap R Bp) P hP
    K.derived K.counit K.universal
  let := K.universal
  let E := ModuleCat.extendScalars.{u} (algebraMap B Bp)
  let η := secondLocalizationDerivedMap R A B Bp D hflat Q L K
  have hηP : IsIso (η.app (DerivedCategory.Qh.obj (q.obj P))) := by
    let β := Functor.whiskerRight L.counit E.mapDerivedCategory ≫
      Functor.whiskerLeft
        ((ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ))
        E.mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
        ((ModuleCat.extendScalarsComp (algebraMap R B) (algebraMap B Bp)).symm ≪≫
          eqToIso (congrArg (fun f : R →+* Bp ↦ ModuleCat.extendScalars.{u} f)
            (IsScalarTower.algebraMap_eq R B Bp).symm)) (.up ℤ)).hom
        DerivedCategory.Qh
    have hf : η.app (DerivedCategory.Qh.obj (q.obj P)) ≫ K.counit.app (q.obj P) =
        β.app (q.obj P) :=
      Functor.leftDerived_fac_app K.derived K.counit
        (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))
        (L.derived ⋙ E.mapDerivedCategory) β (q.obj P)
    have : IsIso (η.app (DerivedCategory.Qh.obj (q.obj P)) ≫
        K.counit.app (q.obj P)) := by
      rw [hf]
      dsimp only [β, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (K.counit.app (q.obj P))
  let := hηP
  have hqs : IsIso (DerivedCategory.Qh.map (q.map s)) := by
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
  let := hqs
  have hn := η.naturality (DerivedCategory.Qh.map (q.map s))
  change (L.derived ⋙ E.mapDerivedCategory).map (DerivedCategory.Qh.map (q.map s)) ≫
      η.app (DerivedCategory.Qh.obj (q.obj V)) =
    η.app (DerivedCategory.Qh.obj (q.obj P)) ≫
      K.derived.map (DerivedCategory.Qh.map (q.map s)) at hn
  have : IsIso ((L.derived ⋙ E.mapDerivedCategory).map
      (DerivedCategory.Qh.map (q.map s)) ≫
        η.app (DerivedCategory.Qh.obj (q.obj V))) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((L.derived ⋙ E.mapDerivedCategory).map (DerivedCategory.Qh.map (q.map s))) _

omit [Algebra A D] [Algebra B D] [Algebra Bp D] tAD tBD tApD tBpD tBBpD in
private theorem secondLocalizationCohomologyMap_smul_left
    (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (a : A) (x : L.cohomology i) :
    secondLocalizationCohomologyMap R A B Bp D hflat Q L K i
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
      (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] Bp) •
        (show K.cohomology i from
          secondLocalizationCohomologyMap R A B Bp D hflat Q L K i x) := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  let E := ModuleCat.extendScalars.{u} (algebraMap B Bp)
  let F := restrict R A ⋙ HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙
    DerivedCategory.Qh
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let Hp := DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i
  let η := secondLocalizationDerivedMap R A B Bp D hflat Q L K
  let φ := flatDerivedHomologyIso B Bp hflat i
  let l := (ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
    ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 (L.cohomology i))
  let k := (ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom).map
    ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] Bp) • 𝟙 (K.cohomology i))
  have hcomm : l ≫ secondLocalizationCohomologyMap R A B Bp D hflat Q L K i =
      secondLocalizationCohomologyMap R A B Bp D hflat Q L K i ≫
        (ModuleCat.restrictScalars (algebraMap B Bp)).map k := by
    dsimp only [secondLocalizationCohomologyMap]
    apply (ModuleCat.extendRestrictScalarsAdj (algebraMap B Bp)).homEquiv_naturality_left_square
    apply (cancel_mono (K.cohomologyIso i).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [show k ≫ (K.cohomologyIso i).hom =
      (K.cohomologyIso i).hom ≫ Hp.map (K.derived.map (F.map (a • 𝟙 Q))) from
        K.cohomologyIso_smul i a]
    simp only [← Category.assoc]
    rw [← E.map_comp, L.cohomologyIso_smul i a]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
    change E.map (L.cohomologyIso i).hom ≫ E.map (H.map (L.derived.map
        (F.map (a • 𝟙 Q)))) ≫ φ.inv.app _ ≫ Hp.map (η.app _) =
      E.map (L.cohomologyIso i).hom ≫ φ.inv.app _ ≫ Hp.map (η.app _) ≫
        Hp.map (K.derived.map (F.map (a • 𝟙 Q)))
    have hn := φ.inv.naturality (L.derived.map (F.map (a • 𝟙 Q)))
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    have hη := congrArg Hp.map (η.naturality (F.map (a • 𝟙 Q)))
    simp only [Functor.map_comp, Functor.comp_map] at hη
    exact congrArg (fun f ↦ E.map (L.cohomologyIso i).hom ≫ φ.inv.app _ ≫ f) hη
  exact congrArg (fun f ↦ f x) hcomm

omit [Algebra A D] [Algebra B D] [Algebra Bp D] tAD tBD tApD tBpD tBBpD in
private theorem secondLocalizationCohomologyMap_smul
    (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (t : A ⊗[R] B) (x : L.cohomology i) :
    secondLocalizationCohomologyMap R A B Bp D hflat Q L K i (t • x) =
      Algebra.TensorProduct.map (AlgHom.id R A) (IsScalarTower.toAlgHom R B Bp) t •
        (show K.cohomology i from
          secondLocalizationCohomologyMap R A B Bp D hflat Q L K i x) := by
  let α := secondLocalizationCohomologyMap R A B Bp D hflat Q L K i
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, add_smul, ht, ht']
  | tmul a b =>
    have ht : a ⊗ₜ[R] b =
        Algebra.TensorProduct.includeLeft (S := R) a *
          Algebra.TensorProduct.includeRight (R := R) (A := A) b := by
      simp [Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight,
        Algebra.TensorProduct.tmul_mul_tmul]
    rw [ht, mul_smul, secondLocalizationCohomologyMap_smul_left]
    have hb : α ((Algebra.TensorProduct.includeRight (R := R) (A := A) b) • x) =
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (algebraMap B Bp b)) •
          (show K.cohomology i from α x) := α.hom.map_smul b x
    rw [hb]
    simp only [AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      IsScalarTower.coe_toAlgHom']
    rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]


omit [Algebra A D] [Algebra B D] [Algebra Bp D] tAD tBD tApD tBpD tBBpD in
private theorem secondLocalization_tensor_adjunct_isIso
    (T : Submonoid B) [IsLocalization T Bp] (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (g : L.cohomology i ⟶ (ModuleCat.restrictScalars
      (Algebra.TensorProduct.map (AlgHom.id R A)
        (IsScalarTower.toAlgHom R B Bp)).toRingHom).obj (K.cohomology i))
    (hg : ∀ x : L.cohomology i, g x =
      secondLocalizationCohomologyMap R A B Bp D hflat Q L K i x) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj
      (Algebra.TensorProduct.map (AlgHom.id R A)
        (IsScalarTower.toAlgHom R B Bp)).toRingHom).homEquiv _ _).symm g) := by
  classical
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  let α := secondLocalizationCohomologyMap R A B Bp D hflat Q L K i
  let β := ((ModuleCat.extendRestrictScalarsAdj (algebraMap B Bp)).homEquiv _ _).symm α
  have hβ : IsIso β := by
    let := secondLocalizationDerivedMap_app_isIso R A B Bp D hflat Q L K
      ((restrict R A).obj Q)
    dsimp only [β, α, secondLocalizationCohomologyMap]
    rw [Equiv.symm_apply_apply]
    infer_instance
  let := hβ
  let φ := (Algebra.TensorProduct.map (AlgHom.id R A)
    (IsScalarTower.toAlgHom R B Bp)).toRingHom
  let _ : Algebra (A ⊗[R] B) (A ⊗[R] Bp) := φ.toAlgebra
  let _ : Module B (L.cohomology i) := Module.compHom _
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let _ : Module Bp (K.cohomology i) := Module.compHom _
    (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom
  let _ : Module B (K.cohomology i) := Module.compHom _ (algebraMap B Bp)
  let _ : Module (A ⊗[R] B) (K.cohomology i) := Module.compHom _ φ
  let _ : IsScalarTower B Bp (K.cohomology i) := IsScalarTower.of_compHom B Bp (K.cohomology i)
  let α₀ : L.cohomology i →ₗ[B] K.cohomology i := α.hom
  let γ : L.cohomology i →ₗ[A ⊗[R] B] K.cohomology i := g.hom
  have hbc : IsBaseChange Bp α₀ := by
    apply IsBaseChange.of_lift_unique
    intro P _ _ _ _ k
    let _ : AddCommGroup P := Module.addCommMonoidToAddCommGroup Bp
    let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap B Bp)
    let k₀ : (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj
          (L.cohomology i) ⟶
        (ModuleCat.restrictScalars (algebraMap B Bp)).obj (ModuleCat.of Bp P) :=
      ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (algebraMap B Bp)).obj
        (ModuleCat.of Bp P))
        { toFun := k
          map_add' := k.map_add
          map_smul' := fun b x ↦ (k.map_smul b x).trans
            (algebraMap_smul (R := B) (A := Bp) b (k x)).symm }
    let h := inv β ≫ (adj.homEquiv _ _).symm k₀
    have hh : α ≫ (ModuleCat.restrictScalars (algebraMap B Bp)).map h = k₀ := by
      rw [← (adj.homEquiv _ _).apply_symm_apply α,
        ← adj.homEquiv_naturality_right]
      change (adj.homEquiv _ _) (β ≫ inv β ≫ (adj.homEquiv _ _).symm k₀) = k₀
      simp only [IsIso.hom_inv_id_assoc, Equiv.apply_symm_apply]
    let hlin : K.cohomology i →ₗ[Bp] P := h.hom
    refine ⟨hlin, ?_, ?_⟩
    · ext x
      exact congrArg (fun f ↦ f x) hh
    · intro l hl
      let l₀ : (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom).obj
            (K.cohomology i) ⟶ ModuleCat.of Bp P := ModuleCat.ofHom l
      have hl₀ : α ≫ (ModuleCat.restrictScalars (algebraMap B Bp)).map l₀ = k₀ := by
        ext x
        exact congrArg (fun f ↦ f x) hl
      have heq : l₀ = h := by
        apply (cancel_epi β).1
        apply (adj.homEquiv _ _).injective
        rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
        rw [hl₀]
        simp only [h, IsIso.hom_inv_id_assoc, Equiv.apply_symm_apply]
      exact LinearMap.ext (fun x ↦ congrArg (fun f ↦ f x) heq)
  let _ : IsLocalizedModule T α₀ :=
    (isLocalizedModule_iff_isBaseChange T Bp α₀).2 hbc
  have hr : (algebraMap (A ⊗[R] B) (A ⊗[R] Bp)).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom =
      (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom.comp
        (algebraMap B Bp) := by
    change φ.comp _ = _
    ext b
    simp [φ, Algebra.TensorProduct.includeRight]
  let _ : IsScalarTower B (A ⊗[R] B) (L.cohomology i) :=
    IsScalarTower.of_compHom B (A ⊗[R] B) (L.cohomology i)
  let _ : IsScalarTower B (A ⊗[R] B) (K.cohomology i) :=
    IsScalarTower.of_algebraMap_smul (R := B) (A := A ⊗[R] B)
      (M := K.cohomology i) (fun b x ↦ by
      change φ ((1 : A) ⊗ₜ[R] b) • x =
        ((1 : A) ⊗ₜ[R] algebraMap B Bp b) • x
      exact congrArg (fun t : A ⊗[R] Bp ↦ t • x) (RingHom.congr_fun hr b))
  have hrestrict : γ.restrictScalars B = α₀ := by
    ext x
    exact hg x
  let _ : IsLocalizedModule T (γ.restrictScalars B) := by
    rw [hrestrict]
    infer_instance
  let _ : IsLocalizedModule (Algebra.algebraMapSubmonoid (A ⊗[R] B) T) γ :=
    IsLocalizedModule.of_restrictScalars T γ
  let _ : IsScalarTower A (A ⊗[R] B) (A ⊗[R] Bp) :=
    IsScalarTower.of_algebraMap_eq' (by
      change _ = φ.comp _
      ext a
      simp [φ])
  let _ : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[R] B) T) (A ⊗[R] Bp) :=
    IsLocalization.tensorProduct_tensorProduct_right R A T Bp hr
  let _ : IsScalarTower (A ⊗[R] B) (A ⊗[R] Bp) (K.cohomology i) :=
    IsScalarTower.of_compHom (A ⊗[R] B) (A ⊗[R] Bp) (K.cohomology i)
  have hc := IsLocalizedModule.isBaseChange
    (Algebra.algebraMapSubmonoid (A ⊗[R] B) T) (A ⊗[R] Bp) γ
  let _ : Module (A ⊗[R] B) (A ⊗[R] Bp) := Module.compHom _ φ
  rw [ConcreteCategory.isIso_iff_bijective]
  have hb := hc.equiv.bijective
  change Function.Bijective (fun x ↦ _) at hb
  convert hb using 1
  ext x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t x =>
    change _ = hc.equiv (t ⊗ₜ[A ⊗[R] B] x)
    rw [IsBaseChange.equiv_tmul]
    rfl

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)] in
private theorem secondLocalization_algebraMap_comp :
    (algebraMap (A ⊗[R] Bp) D).comp
        (Algebra.TensorProduct.map (AlgHom.id R A)
          (IsScalarTower.toAlgHom R B Bp)).toRingHom =
      algebraMap (A ⊗[R] B) D := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a b =>
    change algebraMap (A ⊗[R] Bp) D (a ⊗ₜ[R] algebraMap B Bp b) =
      algebraMap (A ⊗[R] B) D (a ⊗ₜ[R] b)
    have hs (a : A) (b : B) : a ⊗ₜ[R] b =
        (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hs' (a : A) (b : Bp) : a ⊗ₜ[R] b =
        (a ⊗ₜ[R] (1 : Bp)) * ((1 : A) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hs', hs, map_mul, map_mul]
    have hl : algebraMap (A ⊗[R] B) D (a ⊗ₜ[R] (1 : B)) =
        algebraMap A D a := (IsScalarTower.algebraMap_apply A (A ⊗[R] B) D a).symm
    have hl' : algebraMap (A ⊗[R] Bp) D (a ⊗ₜ[R] (1 : Bp)) =
        algebraMap A D a := (IsScalarTower.algebraMap_apply A (A ⊗[R] Bp) D a).symm
    have hr : algebraMap (A ⊗[R] B) D ((1 : A) ⊗ₜ[R] b) =
        algebraMap B D b := (IsScalarTower.algebraMap_apply B (A ⊗[R] B) D b).symm
    have hr' : algebraMap (A ⊗[R] Bp) D ((1 : A) ⊗ₜ[R] algebraMap B Bp b) =
        algebraMap Bp D (algebraMap B Bp b) :=
      (IsScalarTower.algebraMap_apply Bp (A ⊗[R] Bp) D (algebraMap B Bp b)).symm
    rw [hl, hl', hr, hr', ← IsScalarTower.algebraMap_apply B Bp D]


/-- The canonical characterized coefficient map exists before proving it invertible.
Source: Stacks Project, Tag 0DJ8, affine localization identity; Tag 06Y6.
(blueprint: lem-pc-second-localization-iso-aux-hom)

Proof: naturality of the derived comparison and flat homology comparison,
together with the model cohomology action compatibility, shows that the
canonical cohomology map is semilinear for A tensor_R B to A tensor_R Bp.
Take its scalar-extension adjoint and extend further to D. The scalar-tower
hypotheses identify the two maps to D, so the scalar-extension associator
gives the required source. Its formula on 1 tensor x and the adjunction
generator formula give exactly `IsSecondLocalizationMap`.
-/
theorem exists_secondLocalization_hom
    (T : Submonoid B) [IsLocalization T Bp] (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D) :
    ∃ f : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i),
      IsSecondLocalizationMap R A B Bp D hflat Q L K i f := by
  let φ := (Algebra.TensorProduct.map (AlgHom.id R A)
    (IsScalarTower.toAlgHom R B Bp)).toRingHom
  let α := secondLocalizationCohomologyMap R A B Bp D hflat Q L K i
  let _ : Module (A ⊗[R] B) (K.cohomology i) := Module.compHom _ φ
  let g : L.cohomology i ⟶ (ModuleCat.restrictScalars φ).obj (K.cohomology i) :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars φ).obj (K.cohomology i))
      { toFun := fun x ↦ show (ModuleCat.restrictScalars φ).obj (K.cohomology i) from α x
        map_add' := α.hom.map_add
        map_smul' := by
          intro t x
          exact secondLocalizationCohomologyMap_smul R A B Bp D hflat i Q L K t x }
  let g₀ := ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm g
  let E := ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)
  have hφ := secondLocalization_algebraMap_comp R A B Bp D
  let ι := (ModuleCat.extendScalarsComp φ (algebraMap (A ⊗[R] Bp) D)).app
    (L.cohomology i)
  let h := congrArg (fun k : A ⊗[R] B →+* D ↦
    (ModuleCat.extendScalars k).obj (L.cohomology i)) hφ.symm
  refine ⟨(eqToIso h).hom ≫ ι.hom ≫ E.map g₀, ?_⟩
  intro x
  change E.map g₀ (ι.hom ((eqToIso h).hom
    ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x))) = _
  rw [RingTensorCohomology.extendScalars_eqToIso_one_tmul _ _ hφ.symm]
  have hι : ι.hom
      ((1 : D) ⊗ₜ[A ⊗[R] B,(algebraMap (A ⊗[R] Bp) D).comp φ] x) =
      (1 : D) ⊗ₜ[A ⊗[R] Bp,algebraMap (A ⊗[R] Bp) D]
        ((1 : A ⊗[R] Bp) ⊗ₜ[A ⊗[R] B,φ] x) :=
    ModuleCat.extendScalarsComp_hom_app_one_tmul φ (algebraMap (A ⊗[R] Bp) D)
      (L.cohomology i) x
  rw [hι]
  change E.map g₀ ((1 : D) ⊗ₜ[A ⊗[R] Bp,algebraMap (A ⊗[R] Bp) D]
    ((1 : A ⊗[R] Bp) ⊗ₜ[A ⊗[R] B,φ] x)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  have hg : g₀ ((1 : A ⊗[R] Bp) ⊗ₜ[A ⊗[R] B,φ] x) = α x := by
    have hgen := congrArg (fun f ↦ f x)
      (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).apply_symm_apply g)
    exact hgen
  exact congrArg (fun y ↦ (1 : D) ⊗ₜ[A ⊗[R] Bp,algebraMap (A ⊗[R] Bp) D] y) hg


/-- A characterized second-localization map is invertible.
Source: Stacks Project, Tag 0DJ8, affine localization identity; Tag 06Y6.
(blueprint: lem-pc-second-localization-iso-aux-isIso)

Proof: take a common functorial K-flat resolution of the R-restriction of Q.
The universal scalar-extension counits are invertible on that resolution.
Their defining comparison equation proves the derived comparison invertible
there, and naturality transports this to Q. Flat extension commutes with
homology, giving the Bp-base-change universal property of the canonical map.
Its A-semilinearity and the localized-module restriction theorem promote
this to base change over A tensor_R Bp. Extend the resulting isomorphism
further to D, using the tensor associator. The generator formula and
`IsSecondLocalizationMap.ext` identify it with the chosen map.
-/
theorem secondLocalization_hom_isIso
    (T : Submonoid B) [IsLocalization T Bp] (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (f : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i))
    (hf : IsSecondLocalizationMap R A B Bp D hflat Q L K i f) : IsIso f := by
  let φ := (Algebra.TensorProduct.map (AlgHom.id R A)
    (IsScalarTower.toAlgHom R B Bp)).toRingHom
  let α := secondLocalizationCohomologyMap R A B Bp D hflat Q L K i
  let _ : Module (A ⊗[R] B) (K.cohomology i) := Module.compHom _ φ
  let g : L.cohomology i ⟶ (ModuleCat.restrictScalars φ).obj (K.cohomology i) :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars φ).obj (K.cohomology i))
      { toFun := fun x ↦ show (ModuleCat.restrictScalars φ).obj (K.cohomology i) from α x
        map_add' := α.hom.map_add
        map_smul' := by
          intro t x
          exact secondLocalizationCohomologyMap_smul R A B Bp D hflat i Q L K t x }
  let g₀ := ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm g
  let := secondLocalization_tensor_adjunct_isIso R A B Bp D T hflat i Q L K g
    (fun _ ↦ rfl)
  let E := ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)
  have hφ := secondLocalization_algebraMap_comp R A B Bp D
  let ι := (ModuleCat.extendScalarsComp φ (algebraMap (A ⊗[R] Bp) D)).app
    (L.cohomology i)
  let h := congrArg (fun k : A ⊗[R] B →+* D ↦
    (ModuleCat.extendScalars k).obj (L.cohomology i)) hφ.symm
  let f₀ := (eqToIso h).hom ≫ ι.hom ≫ E.map g₀
  have hc : IsSecondLocalizationMap R A B Bp D hflat Q L K i f₀ := by
    intro x
    change E.map g₀ (ι.hom ((eqToIso h).hom
      ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x))) = _
    rw [RingTensorCohomology.extendScalars_eqToIso_one_tmul _ _ hφ.symm]
    have hι : ι.hom
        ((1 : D) ⊗ₜ[A ⊗[R] B,(algebraMap (A ⊗[R] Bp) D).comp φ] x) =
        (1 : D) ⊗ₜ[A ⊗[R] Bp,algebraMap (A ⊗[R] Bp) D]
          ((1 : A ⊗[R] Bp) ⊗ₜ[A ⊗[R] B,φ] x) :=
      ModuleCat.extendScalarsComp_hom_app_one_tmul φ (algebraMap (A ⊗[R] Bp) D)
        (L.cohomology i) x
    rw [hι]
    change E.map g₀ ((1 : D) ⊗ₜ[A ⊗[R] Bp,algebraMap (A ⊗[R] Bp) D]
      ((1 : A ⊗[R] Bp) ⊗ₜ[A ⊗[R] B,φ] x)) = _
    rw [ModuleCat.ExtendScalars.map_tmul]
    have hg : g₀ ((1 : A ⊗[R] Bp) ⊗ₜ[A ⊗[R] B,φ] x) = α x := by
      have hgen := congrArg (fun f ↦ f x)
        (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).apply_symm_apply g)
      exact hgen
    exact congrArg (fun y ↦ (1 : D) ⊗ₜ[A ⊗[R] Bp,algebraMap (A ⊗[R] Bp) D] y) hg
  have heq : f = f₀ := IsSecondLocalizationMap.ext R A B Bp D hf hc
  rw [heq]
  dsimp only [f₀]
  infer_instance

end RingTensorCohomology
