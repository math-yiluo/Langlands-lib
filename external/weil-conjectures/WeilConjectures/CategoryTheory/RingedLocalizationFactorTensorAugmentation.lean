/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedExtendedCech
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # The tensor augmentation for one localization factor

Source: Stacks Project, algebraization.tex, Tag 099B.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local irreducible] SheafOfModules.monoidalCategory

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

private theorem tensor_split_exact
    {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A]
    [∀ K L : CochainComplex A ℤ,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor A) (.up ℤ)]
    (K : CochainComplex A ℤ) (S : ShortComplex (CochainComplex A ℤ))
    (hS : ∀ n : ℤ, (S.map (HomologicalComplex.eval A (.up ℤ) n)).Splitting) :
    (S.map (((curriedTensor A).map₂CochainComplex).obj K)).ShortExact := by
  classical
  let r₀ (q : ℤ) : S.X₂.X q ⟶ S.X₁.X q := (hS q).r
  let s₀ (q : ℤ) : S.X₃.X q ⟶ S.X₂.X q := (hS q).s
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let r : (HomologicalComplex.mapBifunctor K S.X₂ (curriedTensor A) (.up ℤ)).X n ⟶
      (HomologicalComplex.mapBifunctor K S.X₁ (curriedTensor A) (.up ℤ)).X n :=
    HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦ K.X p ◁ r₀ q ≫
      HomologicalComplex.ιMapBifunctor K S.X₁ (curriedTensor A) (.up ℤ) p q n hpq)
  let t : (HomologicalComplex.mapBifunctor K S.X₃ (curriedTensor A) (.up ℤ)).X n ⟶
      (HomologicalComplex.mapBifunctor K S.X₂ (curriedTensor A) (.up ℤ)).X n :=
    HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦ K.X p ◁ s₀ q ≫
      HomologicalComplex.ιMapBifunctor K S.X₂ (curriedTensor A) (.up ℤ) p q n hpq)
  apply ShortComplex.Splitting.shortExact
  refine { r := r, s := t, f_r := ?_, s_g := ?_, id := ?_ }
  · change (HomologicalComplex.mapBifunctorMap (𝟙 K) S.f (curriedTensor A) (.up ℤ)).f n ≫
      r = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp only [r, HomologicalComplex.ι_mapBifunctorMap_assoc,
      HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.id_f,
      curriedTensor_map_app, curriedTensor_obj_map, id_whiskerRight,
      Category.comp_id]
    erw [Category.id_comp]
    rw [← Category.assoc, ← whiskerLeft_comp]
    have h := (hS q).f_r
    change S.f.f q ≫ r₀ q = 𝟙 _ at h
    rw [h, whiskerLeft_id]
    exact Category.id_comp _
  · change t ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 K) S.g (curriedTensor A) (.up ℤ)).f n = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp only [t, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc,
      HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
      curriedTensor_map_app, curriedTensor_obj_map, id_whiskerRight,
      Category.comp_id]
    erw [Category.id_comp]
    rw [← Category.assoc, ← whiskerLeft_comp]
    have h := (hS q).s_g
    change s₀ q ≫ S.g.f q = 𝟙 _ at h
    rw [h, whiskerLeft_id]
    exact Category.id_comp _
  · change r ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 K) S.f (curriedTensor A) (.up ℤ)).f n +
      (HomologicalComplex.mapBifunctorMap (𝟙 K) S.g (curriedTensor A) (.up ℤ)).f n ≫ t = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp only [r, t, Preadditive.comp_add, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc_assoc, HomologicalComplex.ι_mapBifunctorMap,
      HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorDesc,
      HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
      id_whiskerRight, Category.comp_id]
    erw [Category.id_comp, Category.id_comp]
    rw [← Category.assoc, ← whiskerLeft_comp, ← Category.assoc, ← whiskerLeft_comp,
      ← Preadditive.add_comp, ← MonoidalPreadditive.whiskerLeft_add]
    have h := (hS q).id
    change r₀ q ≫ S.f.f q + S.g.f q ≫ s₀ q = 𝟙 _ at h
    rw [h, whiskerLeft_id]
    exact Category.id_comp _

private noncomputable def localization_inclusion
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    (HomologicalComplex.single _ (.up ℤ) 1).obj (ringedSectionLocalization O s) ⟶
      ringedLocalizationTwoTerm O s :=
  HomologicalComplex.mkHomFromSingle (K := ringedLocalizationTwoTerm O s) (j := 1)
    (eqToHom (ringedLocalizationTwoTermX_one O s).symm) (by
      intro k hk
      have hk' : k = 2 := by change (1 : ℤ) + 1 = k at hk; omega
      subst k
      change eqToHom (ringedLocalizationTwoTermX_one O s).symm ≫
        CochainComplex.of.d (ringedLocalizationTwoTermX O s)
          (ringedLocalizationTwoTermD O s) 1 2 = 0
      erw [CochainComplex.of_d]
      simp [ringedLocalizationTwoTermD])

private theorem localization_inclusion_augmentation
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    localization_inclusion O s ≫ ringedLocalizationTwoTermAugmentation O s = 0 := by
  apply HomologicalComplex.from_single_hom_ext
  simp [HomologicalComplex.comp_f, ringedLocalizationTwoTermAugmentation,
    ringedLocalizationTwoTermAugmentationF]

private noncomputable def localization_split
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℤ) :
    ((ShortComplex.mk (localization_inclusion O s)
      (ringedLocalizationTwoTermAugmentation O s)
      (localization_inclusion_augmentation O s)).map
        (HomologicalComplex.eval _ (.up ℤ) n)).Splitting := by
  by_cases hn : n = 0
  · subst n
    apply ShortComplex.Splitting.ofIsZeroOfIsIso
    · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 1
        (ringedSectionLocalization O s) 0 (by omega)
    · change IsIso (ringedLocalizationTwoTermAugmentationF O s 0)
      dsimp only [ringedLocalizationTwoTermAugmentationF]
      split_ifs with h
      · infer_instance
      · exact (h rfl).elim
  · apply ShortComplex.Splitting.ofIsIsoOfIsZero
    · by_cases hn' : n = 1
      · subst n
        change IsIso ((localization_inclusion O s).f 1)
        dsimp only [localization_inclusion]
        rw [HomologicalComplex.mkHomFromSingle_f]
        infer_instance
      · have hz₁ := HomologicalComplex.isZero_single_obj_X (.up ℤ) 1
          (ringedSectionLocalization O s) n hn'
        have hz₂ : IsZero ((ringedLocalizationTwoTerm O s).X n) := by
          change IsZero (ringedLocalizationTwoTermX O s n)
          simp only [ringedLocalizationTwoTermX, ite_eq_right hn, ite_eq_right hn']
          exact isZero_zero _
        exact ⟨⟨0, hz₁.eq_of_src _ _, hz₂.eq_of_src _ _⟩⟩
    · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) n hn

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

private theorem acyclic_shift
    {A : Type*} [Category* A] [Abelian A] (K : CochainComplex A ℤ)
    (hK : K.Acyclic) (a : ℤ) : (K⟦a⟧).Acyclic := by
  intro n
  exact ShortComplex.exact_of_iso
    ((CochainComplex.shiftShortComplexFunctorIso A a n (a + n) rfl).app K).symm
    (hK (a + n))

private theorem quasiIso_projection
    {A : Type*} [Category* A] [Abelian A]
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (hK : S.X₁.Acyclic) : QuasiIso S.g := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (HomologicalComplex.homologyMap S.g n) :=
    (hS.homology_exact₂ n).mono_g ((hK n).isZero_homology.eq_zero_of_src _)
  have : Epi (HomologicalComplex.homologyMap S.g n) :=
    (hS.homology_exact₃ n (n + 1) rfl).epi_f
      ((hK (n + 1)).isZero_homology.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- The self-tensor projection for the two-term complex of one localization.

Source: Stacks Project, algebraization.tex, Tag 099B, proof of
`lemma-derived-completion`, the contraction after localizing at a generator.
(auxiliary; not a blueprint node).

Proof: write L = [O -> S] with S = O[1/s] in degrees zero and one.
The map id_L tensor epsilon has target L tensor O[0]. Its kernel is L tensor
S[-1]. The differential O tensor S -> S tensor S is an isomorphism: the
localization unit becomes invertible after tensoring with S, as follows
sectionwise from the uniqueness of localization and then by sheafification.
Its inverse contracts that kernel. The degreewise split kernel sequence
therefore makes the specified projection a quasi-isomorphism. This includes
s = 0 (S is zero), invertible s (L is contractible), and the zero ring.
-/
theorem ringed_localization_factor_tensor_augmentation_quasiIso
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    letI : CategoryTheory.Limits.HasColimitsOfSize.{0, 0} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := (SheafOfModules.tensorClosed O).1.some
    letI := (SheafOfModules.tensorClosed O).2.1.some
    letI : ∀ K L : ringedSiteComplex O, HomologicalComplex.HasMapBifunctor K L
        (MonoidalCategory.curriedTensor (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) (.up ℤ) :=
      fun _ _ _ ↦ CategoryTheory.Limits.HasColimitsOfShape.has_colimit _
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 (ringedLocalizationTwoTerm O s))
      (ringedLocalizationTwoTermAugmentation O s)
      (MonoidalCategory.curriedTensor (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) (.up ℤ)) := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  let : HasColimitsOfSize.{0, 0} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  let : ∀ K L : ringedSiteComplex O, HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) (.up ℤ) :=
    fun _ _ _ ↦ HasColimitsOfShape.has_colimit _
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let L := ringedLocalizationTwoTerm O s
  let S := ringedSectionLocalization O s
  let T := ((curriedTensor A).map₂CochainComplex).obj L
  let E := ShortComplex.mk (localization_inclusion O s)
    (ringedLocalizationTwoTermAugmentation O s) (localization_inclusion_augmentation O s)
  have hE : (E.map T).ShortExact := tensor_split_exact L E (localization_split O s)
  let F := tensorRight S
  let N := (F.mapHomologicalComplex (.up ℤ)).obj L
  have hd : IsIso (N.d 0 1) := by
    change IsIso (F.map (CochainComplex.of.d (ringedLocalizationTwoTermX O s)
      (ringedLocalizationTwoTermD O s) 0 1))
    erw [CochainComplex.of_d]
    dsimp only [ringedLocalizationTwoTermD]
    split_ifs with h
    · simp only [Functor.map_comp]
      have : IsIso (F.map (ringedSectionLocalizationUnit O s)) :=
        localization_unit_tensor_iso O s
      infer_instance
    · exact (h rfl).elim
  have hN : N.Acyclic := acyclic_two_term N (by
    intro n hn hn'
    apply F.map_isZero
    change IsZero (ringedLocalizationTwoTermX O s n)
    simp only [ringedLocalizationTwoTermX, ite_eq_right hn, ite_eq_right hn']
    exact isZero_zero _)
  let eS : (HomologicalComplex.single A (.up ℤ) 1).obj S ≅
      ((HomologicalComplex.single A (.up ℤ) 0).obj S)⟦(-1 : ℤ)⟧ :=
    (((CochainComplex.singleFunctors A).shiftIso (-1) 1 0 (by omega)).app S).symm
  let e : T.obj ((HomologicalComplex.single A (.up ℤ) 1).obj S) ≅ N⟦(-1 : ℤ)⟧ :=
    T.mapIso eS ≪≫
      CochainComplex.mapBifunctorShift₂Iso L
        ((HomologicalComplex.single A (.up ℤ) 0).obj S) (curriedTensor A) (-1) ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor A) S L)
  apply quasiIso_projection (E.map T) hE
  intro n
  exact (acyclic_shift N hN (-1) n).of_iso e.symm

end CategoryTheory
