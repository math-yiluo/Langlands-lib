/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.KFlatRHomCurrying
import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.AlgebraicGeometry.FiniteGeneratorsLocalSpan
import WeilConjectures.AlgebraicGeometry.FiniteIdealGeneratingCover
import WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! The unit-to-complete direction of the extended Cech criterion.

Source: Stacks Project, algebraization.tex, Tags 099B and 099F.
(blueprint: lem-weil-pbc-extended-cech-unit-isIso-implies-complete).

Proof: on a finite-generator slice, tensoring the extended Cech complex with the
localization at a generator makes one two-term factor contractible. Tensor-Hom
adjunction and the invertible completion unit therefore force derived Hom from
each generator localization to vanish. The complete-element predicate is a sheaf
of ideals, so local generation and covering descent give the local completeness
predicate for every section of the ideal. The fraction and sequential models
agree by the localization comparison.
-/

@[expose] public section

set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped BigOperators

namespace CategoryTheory

section LocalCalculation

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})

private theorem localization_isFlat (R : Sheaf J CommRingCat.{u})
    (g : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    SheafOfModules.IsFlat (ringedSectionLocalization R g) := by
  let O := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let F := ringedSectionLocalizationPresheaf R g
  have hflat (V : Cᵒᵖ) : Module.Flat (R.obj.obj V) (F.obj V) := by
    dsimp [F, ringedSectionLocalizationPresheaf, ringedSectionLocalizationCarrier]
    infer_instance
  have hF : PreservesFiniteLimits (tensorRight F) := by
    constructor
    intro K _ _
    have (V : Cᵒᵖ) : Module.Flat (R.obj.obj V) (F.obj V) := hflat V
    exact ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
      (fun V ↦ isLimitOfPreserves
        (tensorRight (show ModuleCat (R.obj.obj V) from F.obj V))
        (isLimitOfPreserves (PresheafOfModules.evaluation O.obj V) hc))⟩⟩⟩
  have : Presheaf.IsLocallyInjective J (𝟙 O.obj) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun _ ↦ Function.injective_id)
  have : Presheaf.IsLocallySurjective J (𝟙 O.obj) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun _ ↦ Function.surjective_id)
  exact (PresheafOfModules.isFlat_sheafification_obj (R := R) (𝟙 O.obj) F hF).2

private theorem localization_unit_tensor_iso
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    letI := SheafOfModules.monoidalCategory O
    IsIso (ringedSectionLocalizationUnit O s ▷ ringedSectionLocalization O s) := by
  classical
  let := SheafOfModules.monoidalCategory O
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let P := ringedSectionLocalizationPresheaf O s
  let U := SheafOfModules.unit R
  let a := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let η := adj.unit
  let f : U.val ⟶ P := P.unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun X ↦ (1 : ringedSectionLocalizationCarrier O s X))
      (fun {_ _} t ↦ ringedSectionLocalizationPresheaf_one_natural O s t))
  have hf (X : Cᵒᵖ) (x : O.obj.obj X) :
      f.app X x = algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O s X) x := by
    change x • (1 : ringedSectionLocalizationCarrier O s X) = _
    simp [Algebra.smul_def]
  have hi (X : Cᵒᵖ) : IsIso ((f ▷ P).app X) := by
    let m : ModuleCat.of (O.obj.obj X)
          (TensorProduct (O.obj.obj X) (ringedSectionLocalizationCarrier O s X)
            (ringedSectionLocalizationCarrier O s X)) ⟶ P.obj X :=
      ModuleCat.ofHom (LinearMap.mul' (O.obj.obj X) (ringedSectionLocalizationCarrier O s X))
    have : IsIso m := (ConcreteCategory.isIso_iff_bijective m).2
      (IsLocalization.bijective_linearMap_mul' (R := O.obj.obj X) (Submonoid.powers (s.val X))
        (ringedSectionLocalizationCarrier O s X))
    have h : (f ▷ P).app X ≫ m =
        (λ_ (ModuleCat.of (O.obj.obj X) (ringedSectionLocalizationCarrier O s X))).hom := by
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      change O.obj.obj X at x
      change ringedSectionLocalizationCarrier O s X at y
      change (LinearMap.mul' (O.obj.obj X) (ringedSectionLocalizationCarrier O s X))
        ((f.app X x) ⊗ₜ[O.obj.obj X] y) = x • y
      rw [hf]
      change algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O s X) x * y =
        x • y
      exact (Algebra.smul_def x y).symm
    have : IsIso ((f ▷ P).app X ≫ m) := h.symm ▸ inferInstance
    exact (isIso_comp_right_iff _ m).1 this
  let e : U.val ⊗ P ≅ P ⊗ P :=
    PresheafOfModules.isoMk (fun X ↦ asIso ((f ▷ P).app X))
      (fun {_ _} t ↦ (f ▷ P).naturality t)
  have he : e.hom = f ▷ P := rfl
  have : IsIso (f ▷ P) := he ▸ inferInstance
  have : Presheaf.IsLocallyInjective J (𝟙 R.obj) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun _ ↦ Function.injective_id)
  have : Presheaf.IsLocallySurjective J (𝟙 R.obj) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun _ ↦ Function.surjective_id)
  obtain ⟨eT, _⟩ := PresheafOfModules.exists_sheafificationTensorIso (R := O) (𝟙 R.obj)
  have hnat := eT.hom.naturality (X := (U.val, P)) (Y := (P, P)) (f, 𝟙 P)
  have ht : a.map f ▷ a.obj P =
      eT.hom.app (U.val, P) ≫ a.map (f ▷ P) ≫ eT.inv.app (P, P) := by
    change (a.map f ⊗ₘ a.map (𝟙 P)) ≫ eT.hom.app (P, P) =
      eT.hom.app (U.val, P) ≫ a.map (f ⊗ₘ 𝟙 P) at hnat
    simp only [Functor.map_id, tensorHom_id] at hnat
    apply (cancel_mono (eT.hom.app (P, P))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact hnat
  have : IsIso (a.map f ▷ a.obj P) := by rw [ht]; infer_instance
  have heq : a.map f = adj.counit.app U ≫ ringedSectionLocalizationUnit O s := by
    apply (adj.homEquiv U.val (a.obj P)).injective
    simp only [Adjunction.homEquiv_unit, Functor.comp_map, Functor.map_comp]
    change η.app U.val ≫ (a.map f).val =
      η.app U.val ≫ (adj.counit.app U).val ≫ (ringedSectionLocalizationUnit O s).val
    have htri : η.app U.val ≫ (adj.counit.app U).val = 𝟙 U.val :=
      adj.right_triangle_components U
    rw [← Category.assoc, htri]
    change η.app U.val ≫ (a.map f).val = 𝟙 U.val ≫ (f ≫ η.app P)
    exact (η.naturality f).symm.trans (Category.id_comp _).symm
  rw [heq, comp_whiskerRight] at this
  exact (isIso_comp_left_iff (adj.counit.app U ▷ a.obj P) _).1 this

private theorem acyclic_two_term
    {A : Type*} [Category* A] [Abelian A] (K : CochainComplex A ℤ)
    (hzero : ∀ n : ℤ, n ≠ 0 → n ≠ 1 → IsZero (K.X n))
    [IsIso (K.d 0 1)] : K.Acyclic := by
  intro n
  by_cases hn : n = 0
  · subst n
    rw [HomologicalComplex.exactAt_iff' K (i := -1) (j := 0) (k := 1)
      (by simp) (by simp)]
    apply (ShortComplex.exact_iff_mono _
      ((hzero (-1) (by omega) (by omega)).eq_zero_of_src _)).2
    change Mono (K.d 0 1)
    infer_instance
  · by_cases hn' : n = 1
    · subst n
      rw [HomologicalComplex.exactAt_iff' K (i := 0) (j := 1) (k := 2)
        (by simp) (by simp)]
      exact (ShortComplex.exact_iff_epi _ ((hzero 2 (by omega) (by omega)).eq_zero_of_tgt _)).2 (by
          change Epi (K.d 0 1)
          infer_instance)
    · exact HomologicalComplex.ExactAt.of_isZero (hzero n hn hn')

private theorem ringComplex_kflat :
    CochainComplex.IsKFlatTensor (ringedSiteRingComplex O) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨0, fun n hn ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n (ne_of_gt hn)
  · intro n
    let := SheafOfModules.monoidalCategory O
    by_cases hn : n = 0
    · subst n
      have h := ObjectProperty.prop_unit
        (ObjectProperty.flat (A := SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))
      exact ((ObjectProperty.flat).prop_of_iso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).symm h).tensorRight
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn)).tensorRight

private theorem localizationFactor_kflat
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    CochainComplex.IsKFlatTensor (ringedLocalizationTwoTerm O s) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨1, fun n hn ↦ ?_⟩
    change IsZero (ringedLocalizationTwoTermX O s n)
    simp only [ringedLocalizationTwoTermX, ite_eq_right (show n ≠ 0 by omega),
      ite_eq_right (show n ≠ 1 by omega)]
    exact isZero_zero _
  · intro n
    change SheafOfModules.IsFlat (ringedLocalizationTwoTermX O s n)
    by_cases hn : n = 0
    · subst n
      rw [ringedLocalizationTwoTermX_zero]
      let := SheafOfModules.monoidalCategory O
      exact (ObjectProperty.prop_unit (ObjectProperty.flat)).tensorRight
    · by_cases hn' : n = 1
      · subst n
        rw [ringedLocalizationTwoTermX_one]
        exact localization_isFlat O s
      · simp only [ringedLocalizationTwoTermX, ite_eq_right hn, ite_eq_right hn']
        let := SheafOfModules.monoidalCategory O
        exact (ObjectProperty.flat_of_isZero (isZero_zero _)).tensorRight

private theorem cech_kflat (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    CochainComplex.IsKFlatTensor (ringedExtendedCech O r b).1 := by
  induction r with
  | zero => exact ringComplex_kflat O
  | succ r ih =>
    let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
    let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    let : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, u, u} _
    let := SheafOfModules.monoidalCategory O
    let := SheafOfModules.symmetricCategory O
    let := (SheafOfModules.tensorClosed O).1.some
    let := (SheafOfModules.tensorClosed O).2.1.some
    intro M hM i
    exact (ih (fun j ↦ b j.succ) _ (localizationFactor_kflat O (b 0) M hM) i).of_iso
      (HomologicalComplex.associator M (ringedLocalizationTwoTerm O (b 0))
        (ringedExtendedCech O r (fun j ↦ b j.succ)).1)

private theorem localized_factor_acyclic
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    letI := SheafOfModules.monoidalCategory O
    (CochainComplex.mapBifunctor
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (ringedSectionLocalization O s))
      (ringedLocalizationTwoTerm O s) (curriedTensor _)).Acyclic := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  let F := tensorLeft (ringedSectionLocalization O s)
  let N := (F.mapHomologicalComplex (.up ℤ)).obj (ringedLocalizationTwoTerm O s)
  have hd : IsIso (N.d 0 1) := by
    change IsIso (F.map (CochainComplex.of.d (ringedLocalizationTwoTermX O s)
      (ringedLocalizationTwoTermD O s) 0 1))
    erw [CochainComplex.of_d]
    dsimp only [ringedLocalizationTwoTermD]
    split_ifs with h
    · simp only [Functor.map_comp]
      have hr := localization_unit_tensor_iso O s
      have hn := BraidedCategory.braiding_naturality_right
        (ringedSectionLocalization O s) (ringedSectionLocalizationUnit O s)
      have hi : IsIso (F.map (ringedSectionLocalizationUnit O s) ≫
          (β_ (ringedSectionLocalization O s) (ringedSectionLocalization O s)).hom) := by
        change IsIso (ringedSectionLocalization O s ◁ ringedSectionLocalizationUnit O s ≫
          (β_ (ringedSectionLocalization O s) (ringedSectionLocalization O s)).hom)
        rw [hn]
        infer_instance
      have : IsIso (F.map (ringedSectionLocalizationUnit O s)) :=
        (isIso_comp_right_iff _ _).1 hi
      infer_instance
    · exact (h rfl).elim
  have hN : N.Acyclic := acyclic_two_term N (by
    intro n hn hn'
    apply F.map_isZero
    change IsZero (ringedLocalizationTwoTermX O s n)
    simp only [ringedLocalizationTwoTermX, ite_eq_right hn, ite_eq_right hn']
    exact isZero_zero _)
  intro n
  exact (hN n).of_iso
    (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) _ _).symm

private theorem localized_cech_acyclic
    (r : ℕ) (b : Fin (r + 1) → (O.obj ⋙ forget CommRingCat).sections) :
    letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := (SheafOfModules.tensorClosed O).1.some
    letI := (SheafOfModules.tensorClosed O).2.1.some
    (CochainComplex.mapBifunctor
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (ringedSectionLocalization O (b 0)))
      (ringedExtendedCech O (r + 1) b).1 (curriedTensor _)).Acyclic := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  let L := ringedLocalizationTwoTerm O (b 0)
  let K := (ringedExtendedCech O r (fun j ↦ b j.succ)).1
  let S := (HomologicalComplex.single A (.up ℤ) 0).obj
    (ringedSectionLocalization O (b 0))
  have hSL := localized_factor_acyclic O (b 0)
  intro n
  exact (cech_kflat O r (fun j ↦ b j.succ) _ hSL n).of_iso
    (HomologicalComplex.associator S L K)

private theorem generatingList_section_value
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (σ : (I.over U).GeneratingSections) (e : σ.I ≃ Fin r)
    (h : ∀ i, (SheafOfModules.sectionsMap (ι.over U) (σ.s i)).val
      (op (Over.mk (𝟙 U))) = f (e i))
    (W : C) (a : W ⟶ U) (i : σ.I) :
    ι.val.app (op W) ((σ.s i).val (op (Over.mk a))) = O.obj.map a.op (f (e i)) := by
  let k : Over.mk a ⟶ Over.mk (𝟙 U) := Over.homMk a (by simp)
  have hn := (SheafOfModules.sectionsMap (ι.over U) (σ.s i)).property k.op
  change O.obj.map a.op
    ((SheafOfModules.sectionsMap (ι.over U) (σ.s i)).val (op (Over.mk (𝟙 U)))) = _ at hn
  rw [h] at hn
  exact hn.symm

private theorem exists_cover_mem_span_generatingList
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (hf : IsRingedIdealGeneratingList O I ι U r f)
    (W : C) (a : W ⟶ U) {T : Type u} [Finite T]
    (s : T → I.val.obj (op W)) :
    ∃ S ∈ J W, ∀ (V : C) (k : V ⟶ W), S k → ∀ j,
      ι.val.app (op V) (I.val.map k.op (s j)) ∈
        Ideal.span (Set.range (fun i ↦ O.obj.map (k ≫ a).op (f i))) := by
  classical
  obtain ⟨σ, e, he⟩ := hf
  let := Fintype.ofEquiv (Fin r) e.symm
  obtain ⟨S, hS, hs⟩ := SheafOfModules.exists_cover_linearCombination_generators
    (I.over U) σ (Over.mk a) s
  refine ⟨Sieve.overEquiv (Over.mk a) S, (J.mem_over_iff S).1 hS, ?_⟩
  intro V k hk j
  let l : Over.mk (k ≫ a) ⟶ Over.mk a := Over.homMk k rfl
  have hl : S l := by
    have hh : ((Sieve.overEquiv (Over.mk a)).symm
        (Sieve.overEquiv (Over.mk a) S)) l := hk
    simpa only [OrderIso.symm_apply_apply] using hh
  obtain ⟨c, hc⟩ := hs (Over.mk (k ≫ a)) l hl j
  change I.val.map k.op (s j) = ∑ i, c i •
    (show I.val.obj (op V) from (σ.s i).val (op (Over.mk (k ≫ a)))) at hc
  rw [hc, map_sum]
  change (∑ i, (show O.obj.obj (op V) from ι.val.app (op V)
    (c i • (show I.val.obj (op V) from (σ.s i).val (op (Over.mk (k ≫ a))))))) ∈ _
  apply Submodule.sum_mem
  intro i _
  have hi := (ι.val.app (op V)).hom.map_smul
    (show ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj.obj (op V) from c i)
    (show I.val.obj (op V) from (σ.s i).val (op (Over.mk (k ≫ a))))
  change (show O.obj.obj (op V) from ι.val.app (op V)
      (c i • (show I.val.obj (op V) from (σ.s i).val (op (Over.mk (k ≫ a)))))) =
    (show O.obj.obj (op V) from c i) *
      (show O.obj.obj (op V) from ι.val.app (op V)
        ((σ.s i).val (op (Over.mk (k ≫ a))))) at hi
  rw [hi, generatingList_section_value O I ι U r f σ e he V (k ≫ a) i]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e i, rfl⟩)

private theorem single_localization_kflat
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    CochainComplex.IsKFlatTensor
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (ringedSectionLocalization O s)) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · exact ⟨0, fun n hn ↦ HomologicalComplex.isZero_single_obj_X _ _ _ _ (ne_of_gt hn)⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      exact (exactFunctor _ _).prop_of_iso
        ((curriedTensor _).flip.mapIso
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).symm)
        (localization_isFlat O s)
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn)).tensorRight

open CategoryTheory.Pretriangulated.Opposite in
private theorem cech_generator_vanishing
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (r : ℕ) (b : Fin (r + 1) → (O.obj ⋙ forget CommRingCat).sections)
    (E : ringedSiteDerived O) :
    IsZero ((derivedInternalHom J O).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (ringedSectionLocalization O (b 0))),
        (ringedCechCompletionFunctor O (ringedExtendedCech O (r + 1) b).1).obj E)) := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, u, u} _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  let S := (HomologicalComplex.single A (.up ℤ) 0).obj (ringedSectionLocalization O (b 0))
  let P : (KFlatRHom.flat O).FullSubcategory := ⟨S, single_localization_kflat O (b 0)⟩
  let L : (KFlatRHom.flat O).FullSubcategory :=
    ⟨(ringedExtendedCech O (r + 1) b).1, cech_kflat O (r + 1) b⟩
  let T := (KFlatRHom.total O).obj (S, L.obj)
  have hT : T.Acyclic := localized_cech_acyclic O r b
  have hz : IsZero (DerivedCategory.Q.obj T) := by
    apply (DerivedCategory.isZero_iff _).2
    intro n
    exact (hT n).isZero_homology.of_iso
      ((DerivedCategory.homologyFunctorFactors A n).app T)
  obtain ⟨shift, hshift⟩ := (ringedInternalHom_exact J O).2 E
  let := shift
  have := hshift
  have hH := ((Functor.curry.obj (derivedInternalHom J O)).flip.obj E).map_isZero hz.op
  exact hH.of_iso ((KFlatRHom.curryIso O).app (op P, op L, E))

end LocalCalculation

/-- An invertible augmented extended Cech unit forces local derived completeness.

Source: Stacks Project, algebraization.tex, Tags 099B and 099F.
(blueprint: lem-weil-pbc-extended-cech-unit-isIso-implies-complete). -/
theorem ringedExtendedCech_unit_isIso_implies_complete
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u}
        ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε)
    (E : ringedSiteDerived O) :
    IsIso (ringedCechCompletionUnit O K ε E) →
      IsLocallyDerivedRingedIdealComplete O I ι E := by
  classical
  intro hunit
  have := hunit
  let (U : C) : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))))
  obtain ⟨S, hmem, hrestrict, hdescent, _⟩ := ringedSite_complete_elements_ideal J O E
  obtain ⟨eR, _, _⟩ := ringedInternalHom_restriction J O
  have hgen (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U))
      (hf : IsRingedIdealGeneratingList O I ι U r f) (i : Fin r) : f i ∈ S U := by
    cases r with
    | zero => exact Fin.elim0 i
    | succ r =>
      let t : Fin (r + 1) ≃ Fin (r + 1) := Equiv.swap 0 i
      let g : Fin (r + 1) → O.obj.obj (op U) := fun j ↦ f (t j)
      have hg : IsRingedIdealGeneratingList O I ι U (r + 1) g := by
        obtain ⟨σ, e, he⟩ := hf
        refine ⟨σ, e.trans t.symm, ?_⟩
        intro j
        simpa only [g, Equiv.trans_apply, Equiv.apply_symm_apply] using he j
      have hzero : g 0 = f i := by simp [g, t]
      rw [← hzero]
      obtain ⟨eK, _⟩ := hK U (r + 1) g hg
      let R := ringedDerivedRestriction O U
      let H := derivedInternalHom (J.over U) (O.over U)
      let P := (ringedExtendedCech (O.over U) (r + 1) (fun j ↦ ringedSliceSection O U (g j))).1
      let eE : R.obj E ≅ (ringedCechCompletionFunctor (O.over U) P).obj (R.obj E) :=
        R.mapIso (asIso (ringedCechCompletionUnit O K ε E)) ≪≫
          (eR U).app (op (DerivedCategory.Q.obj K), E) ≪≫
            H.mapIso (eK.op.prod (Iso.refl (R.obj E)))
      let F := (Functor.curry.obj H).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj
          (ringedSectionLocalization (O.over U) (ringedSliceSection O U (g 0)))))
      have hz := cech_generator_vanishing (O.over U) r
        (fun j ↦ ringedSliceSection O U (g j)) (R.obj E)
      apply (hmem U (g 0)).2
      apply (localCompleteness_models_iff J O E U (g 0)).1
      exact hz.of_iso (F.mapIso eE)
  obtain ⟨A, V, r, b, hV, hb⟩ := exists_finiteIdealGeneratingCover O I ι
  intro U f hf
  apply (localCompleteness_models_iff J O E U f).2
  apply (hmem U f).1
  apply hdescent U _ (hV U) f
  rintro W a ⟨j, ⟨c⟩⟩
  obtain ⟨y, hy⟩ := hf
  obtain ⟨T, hT, ht⟩ := exists_cover_mem_span_generatingList O I ι
    (V j) (r j) (b j) (hb j) W c
    (fun _ : ULift.{u} Unit ↦ I.val.map a.op y)
  apply hdescent W T hT (O.obj.map a.op f)
  intro Z k hk
  have hspan : Ideal.span (Set.range (fun i ↦ O.obj.map (k ≫ c).op (b j i))) ≤ S Z := by
    apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    exact hrestrict (V j) Z (k ≫ c) (b j i) (hgen (V j) (r j) (b j) (hb j) i)
  have hx := hspan (ht Z k hk ⟨()⟩)
  have hn := (PresheafOfModules.naturality_apply ι.val k.op (I.val.map a.op y)).symm
  have ha := (PresheafOfModules.naturality_apply ι.val a.op y).symm
  change O.obj.map k.op (ι.val.app (op W) (I.val.map a.op y)) =
    ι.val.app (op Z) (I.val.map k.op (I.val.map a.op y)) at hn
  change O.obj.map a.op (ι.val.app (op U) y) =
    ι.val.app (op W) (I.val.map a.op y) at ha
  rw [← hn, ← ha, hy] at hx
  exact hx

end CategoryTheory
