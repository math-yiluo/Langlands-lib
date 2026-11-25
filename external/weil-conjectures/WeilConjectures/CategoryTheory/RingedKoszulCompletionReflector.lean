/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModel
import WeilConjectures.CategoryTheory.RingedAugmentedCechRestriction
import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite

/-!
# The strict Koszul completion reflector on a ringed site

Source: Stacks Project, algebraization.tex, Tags 0999, 099B and 0A0E
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

set_option autoImplicit false
set_option synthInstance.maxSize 2048

private theorem complete_of_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    {N M : ringedSiteDerived O} (e : N ≅ M)
    (hN : IsLocallyDerivedRingedIdealComplete O I ι N) :
    IsLocallyDerivedRingedIdealComplete O I ι M := by
  intro U f hf
  let H := derivedInternalHom (J.over U) (O.over U)
  exact (hN U f hf).of_iso
    (H.mapIso ((Iso.refl _).prod ((ringedDerivedRestriction O U).mapIso e))).symm

private theorem finiteType_of_generating_list
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (hgen : ∀ U : C, IsRingedIdealGeneratingList O I ι U r
      (fun i ↦ (b i).val (op U))) : I.IsFiniteType := by
  classical
  choose σ e he using hgen
  let p : I.LocalGeneratorsData :=
    { I := C
      X := id
      coversTop := fun _ ↦ GrothendieckTopology.covering_of_eq_top J (by simp)
      generators := σ }
  apply SheafOfModules.IsFiniteType.mk (M := I)
  refine ⟨p, ?_⟩
  refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := p) (fun U ↦ ?_)
  exact ⟨Finite.of_equiv (Fin r) (e U).symm⟩

private theorem scalar_extension
    {A : Type*} [Category A] [MonoidalCategory A]
    (X : A) (a : X ⟶ 𝟙_ A) (t : 𝟙_ A ≅ 𝟙_ A) :
    ∃ s : X ≅ X, s.hom ≫ a = a ≫ t.hom := by
  let s := (λ_ X).symm ≪≫ (t ⊗ᵢ Iso.refl X) ≪≫ (λ_ X)
  refine ⟨s, ?_⟩
  simp only [s, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    Category.assoc]
  have ht : (t.hom ⊗ₘ 𝟙 (𝟙_ A)) ≫ (λ_ (𝟙_ A)).hom =
      (λ_ (𝟙_ A)).hom ≫ t.hom := by
    simpa only [tensorHom_id, unitors_equal] using rightUnitor_naturality t.hom
  calc
    _ = (λ_ X).inv ≫ ((t.hom ⊗ₘ 𝟙 X) ≫ (𝟙 (𝟙_ A) ⊗ₘ a)) ≫
        (λ_ (𝟙_ A)).hom := by
      simp only [id_tensorHom, Category.assoc, leftUnitor_naturality]
    _ = (λ_ X).inv ≫ (t.hom ⊗ₘ a) ≫ (λ_ (𝟙_ A)).hom := by
      rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    _ = (λ_ X).inv ≫ ((𝟙 (𝟙_ A) ⊗ₘ a) ≫
        (t.hom ⊗ₘ 𝟙 (𝟙_ A))) ≫ (λ_ (𝟙_ A)).hom := by
      rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    _ = _ := by
      simp only [Category.assoc, ht, id_tensorHom,
        leftUnitor_naturality_assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem derived_scalar_extension
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (K : ringedSiteComplex O) (a : K ⟶ ringedSiteRingComplex O)
    (t : DerivedCategory.Q.obj (ringedSiteRingComplex O) ≅
      DerivedCategory.Q.obj (ringedSiteRingComplex O)) :
    ∃ s : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj K,
      s.hom ≫ DerivedCategory.Q.map a = DerivedCategory.Q.map a ≫ t.hom := by
  let A := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let : MonoidalCategory (ringedSiteComplex O) := inferInstance
  let t0 : SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
    (DerivedCategory.singleFunctor A 0).preimageIso t
  let t1 := (HomologicalComplex.single A (.up ℤ) 0).mapIso t0
  obtain ⟨s, hs⟩ := scalar_extension K a t1
  refine ⟨DerivedCategory.Q.mapIso s, ?_⟩
  have ht : DerivedCategory.Q.map t1.hom = t.hom :=
    (DerivedCategory.singleFunctor A 0).map_preimage t.hom
  change DerivedCategory.Q.map s.hom ≫ DerivedCategory.Q.map a = _
  rw [← DerivedCategory.Q.map_comp, hs, Functor.map_comp, ht]

set_option backward.isDefEq.respectTransparency false in
private theorem augmented_restriction_normalized
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (U : C) :
    ∃ e : DerivedCategory.Q.obj (ringedExtendedCech (O.over U) r
          (fun i ↦ ringedKoszulSliceSection O (b i) U)).1 ≅
        (ringedDerivedRestriction O U).obj
          (DerivedCategory.Q.obj (ringedExtendedCech O r b).1),
      e.hom ≫ (ringedDerivedRestriction O U).map
          (DerivedCategory.Q.map (ringedExtendedCech O r b).2) ≫
          (ringedDerivedRingRestrictionIso O U).hom =
        DerivedCategory.Q.map (ringedExtendedCech (O.over U) r
          (fun i ↦ ringedKoszulSliceSection O (b i) U)).2 := by
  obtain ⟨h⟩ := (exists_ringed_augmented_cech_restriction O r b).1 U
  let t := (Arrow.rightFunc.mapIso h).symm ≪≫ ringedDerivedRingRestrictionIso O U
  obtain ⟨s, hs⟩ := derived_scalar_extension (O.over U) _
    (ringedExtendedCech (O.over U) r
      (fun i ↦ ringedKoszulSliceSection O (b i) U)).2 t.symm
  refine ⟨s ≪≫ (Arrow.leftFunc.mapIso h).symm, ?_⟩
  change (s.hom ≫ h.inv.left) ≫ _ ≫ _ = _
  have hw := h.inv.w
  simp only [Arrow.mk_hom] at hw
  simp only [Category.assoc]
  rw [reassoc_of% hw]
  have hh : h.hom.right ≫ h.inv.right = 𝟙 _ :=
    congrArg (fun f ↦ f.right) h.hom_inv_id
  rw [← Category.assoc s.hom, hs]
  simp only [t, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Functor.mapIso_hom,
    Arrow.rightFunc_map,
    Category.assoc]
  rw [← Category.assoc h.hom.right, hh]
  simp only [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem generating_list_localDescription
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (hgen : ∀ U : C, IsRingedIdealGeneratingList O I ι U r
      (fun i ↦ (b i).val (op U))) :
    HasLocalExtendedCechDescription O I ι (ringedExtendedCech O r b).1
      (ringedExtendedCech O r b).2 := by
  obtain ⟨K, ε, hK⟩ := exists_ringedExtendedCech_global_model J O I ι
  intro U n f hf
  obtain ⟨a, ha⟩ := hK U n f hf
  have hs := hK U r (fun i ↦ (b i).val (op U)) (hgen U)
  have heq : (fun i ↦ ringedSliceSection O U ((b i).val (op U))) =
      (fun i ↦ ringedKoszulSliceSection O (b i) U) := by
    funext i
    apply Subtype.ext
    funext V
    exact (b i).property V.unop.hom.op
  change ∃ c : DerivedCategory.Q.obj (ringedExtendedCech (O.over U) r
      (fun i ↦ ringedSliceSection O U ((b i).val (op U)))).1 ≅ _, _ at hs
  rw [heq] at hs
  obtain ⟨c, hc⟩ := hs
  obtain ⟨d, hd⟩ := augmented_restriction_normalized O r b U
  refine ⟨a ≪≫ c.symm ≪≫ d, ?_⟩
  have hc' : c.inv ≫ DerivedCategory.Q.map
      (ringedExtendedCech (O.over U) r
        (fun i ↦ ringedKoszulSliceSection O (b i) U)).2 =
      (ringedDerivedRestriction O U).map (DerivedCategory.Q.map ε) ≫
        (ringedDerivedRingRestrictionIso O U).hom := by
    rw [← hc, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hd, hc']
  simpa only [Category.assoc] using ha

/-- The total derived inverse limit of the strict negative Koszul tower is the reflector
onto locally derived complete objects, with its prescribed degree-zero unit.

Source: Stacks Project, algebraization.tex, Tags 0999 (definition-derived-complete),
099B (lemma-derived-completion), 0A0E (lemma-derived-completion-koszul)
(auxiliary; not a blueprint node).

The mono `ι` represents the ideal generated by `b`: `_hgen` specifies its generators on
all slices, so it is exactly the ideal sheaf in the source, not an additional hypothesis
on that ideal. The finite list includes the empty list. Index `m : ℕ` means power `m+1`.
`RingedKoszulLimitPresentation` fixes the actual dual Koszul tensor tower and transitions,
its descent through localization, total right derived inverse limit with its comparison
and computation on K-injective strict towers, and the unit induced by the degree-zero maps.
No exactness of products and no boundedness are assumed.

Proof plan:
1. Use lem-weil-pbc-ringed-cech-koszul-dual-limit to compare the Cech internal-Hom
   functor with the strict tensor-tower limit. The comparison preserves the unit and
   dualizes forward maps (1,b_i) to inverse maps (b_i,1). The strict-tower theorem fixes
   total derived inverse limit without exactness of sheaf products.
2. On each slice use lem-weil-pbc-ringed-localization-rhom-calculus to curry internal
   Hom from localization at b_i. The localized Cech complex contracts by inserting i:
   the sign is (-1) to the number of preceding indices, and the deletion terms cancel.
3. Apply lem-weil-pbc-ringed-derived-complete-elements-ideal: vanishing for generators
   implies vanishing for every local section of their generated ideal, by ideal closure
   and descent. For the empty list the zero section localizes to the zero sheaf.
4. Verify the local-description hypothesis of lem-weil-pbc-extended-cech-completion-model.
   The ideal is finite type. On a slice compare any two generating lists to the model
   supplied by its existence clause; compose their augmentation-compatible isomorphisms.
   Its reflection clause then supplies the Hom bijection for the Cech functor.
5. Transport that bijection across the unit-compatible Koszul comparison theta. Send a
   map a:N -> L to the unique u:F(N) -> L extending a, composed with theta inverse.
   The two inverse identities follow from uniqueness and theta etaC = eta.
6. For complete N, the Cech unit and theta are isomorphisms. Conversely an invertible
   strict unit transports output completeness back to N on every slice.
7. Functoriality of internal Hom and naturality of theta give naturality of the strict
   unit, and the representative comparison makes the construction a derived functor. -/
theorem ringedKoszulCompletionReflector
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι]
    (_hgen : ∀ U : C, IsRingedIdealGeneratingList O I ι U r
      (fun i ↦ (b i).val (op U))) :
    ∃ D : RingedKoszulLimitPresentation O r b,
      (∀ N : ringedSiteDerived O,
        IsLocallyDerivedRingedIdealComplete O I ι (D.completion.obj N)) ∧
      (∀ (N L : ringedSiteDerived O), IsLocallyDerivedRingedIdealComplete O I ι L →
        Function.Bijective (fun a : D.completion.obj N ⟶ L ↦ D.unit N ≫ a)) ∧
      (∀ N : ringedSiteDerived O,
        IsIso (D.unit N) ↔ IsLocallyDerivedRingedIdealComplete O I ι N) ∧
      (∀ (N N' : ringedSiteDerived O) (a : N ⟶ N'),
        D.unit N ≫ D.completion.map a = a ≫ D.unit N') := by
  classical
  have : I.IsFiniteType := finiteType_of_generating_list O I ι r b _hgen
  let K := (ringedExtendedCech O r b).1
  let ε := (ringedExtendedCech O r b).2
  have hK : HasLocalExtendedCechDescription O I ι K ε :=
    generating_list_localDescription O r b I ι _hgen
  obtain ⟨hc, hn, hb, hi⟩ := ringedExtendedCech_reflector_properties J O I ι K ε hK
  obtain ⟨D, theta, htheta⟩ := exists_ringed_cech_koszul_comparison_on_site O r b
  change ∀ N, ringedCechCompletionUnit O K ε N ≫ theta.hom.app N = D.unit N at htheta
  have hcD (N : ringedSiteDerived O) :
      IsLocallyDerivedRingedIdealComplete O I ι (D.completion.obj N) :=
    complete_of_iso O I ι (theta.app N) (hc N)
  have hbD (N L : ringedSiteDerived O)
      (hL : IsLocallyDerivedRingedIdealComplete O I ι L) :
      Function.Bijective (fun a : D.completion.obj N ⟶ L ↦ D.unit N ≫ a) := by
    constructor
    · intro a a' h
      apply (cancel_epi (theta.hom.app N)).1
      apply (hb N L hL).1
      dsimp only
      rw [← Category.assoc, ← Category.assoc, htheta N]
      exact h
    · intro a
      obtain ⟨g, hg⟩ := (hb N L hL).2 a
      refine ⟨theta.inv.app N ≫ g, ?_⟩
      rw [← htheta N]
      simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hg
  refine ⟨D, hcD, hbD, ?_, ?_⟩
  · intro N
    constructor
    · intro h
      exact complete_of_iso O I ι (asIso (D.unit N)).symm (hcD N)
    · intro h
      have := hi N h
      rw [← htheta N]
      infer_instance
  · intro N N' a
    rw [← htheta N, Category.assoc, ← theta.hom.naturality,
      ← Category.assoc, hn N N' a, Category.assoc, htheta N']

end CategoryTheory
