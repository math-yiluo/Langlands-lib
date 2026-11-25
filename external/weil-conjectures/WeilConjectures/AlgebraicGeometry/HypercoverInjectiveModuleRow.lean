/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverResolution
public import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.RingedHypercoverInjectiveAugmentationRing
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Injective hypercover rows over arbitrary rings

Source: Stacks Project, Hypercoverings, Tag 01GW.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/- The scalar-extension construction of
WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence uses only left
modules and RingCat. Reproduce its arbitrary-ring form privately: the adopted source
keeps its CommRing interface. Source: Stacks, Modules on Sites, Sections 093I and 03CV,
and Sites Example 0H7J. The unit and counit below are identities on abelian sections. -/
section ConstantScalars

noncomputable section

variable (Y : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

private abbrev rowConstantModuleRing : Sheaf Y.smallEtaleTopology RingCat.{u + 1} :=
  (constantSheaf Y.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)

set_option backward.isDefEq.respectTransparency false in
private def rowConstantModulePresheaf (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    PresheafOfModules.{u + 1} ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ)) :=
  letI (X : Y.Etaleᵒᵖ) : Module
      (((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ)).obj X)
      ((J.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj X) :=
    (J.obj.obj X).isModule
  PresheafOfModules.ofPresheaf
    (R := (Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ))
    (J.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    (fun {_ _} f r m ↦ (J.obj.map f).hom.map_smul r m)

set_option backward.isDefEq.respectTransparency false in
private def rowConstantModuleRealization
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    SheafOfModules.{u + 1} (rowConstantModuleRing Y Λ) :=
  PresheafOfModules.sheafify
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ)))
    (M₀ := rowConstantModulePresheaf Y Λ J)
    (A := (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J)
    (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
private def rowConstantModuleFunctor :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      SheafOfModules.{u + 1} (rowConstantModuleRing Y Λ) where
  obj J := rowConstantModuleRealization Y Λ J
  map {J K} f := PresheafOfModules.sheafifyMap _ _ _
    (PresheafOfModules.homMk
      (M₁ := rowConstantModulePresheaf Y Λ J)
      (M₂ := rowConstantModulePresheaf Y Λ K)
      (Functor.whiskerRight f.hom (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
      (fun X r m ↦ (f.hom.app X).hom.map_smul r m))
    ((sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map f)
    (by ext X x; rfl)
  map_id J := by ext X x; rfl
  map_comp f g := by ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
private def rowConstantModuleRestriction
    (M : SheafOfModules.{u + 1} (rowConstantModuleRing Y Λ)) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj :=
    let P := (PresheafOfModules.restrictScalars
      (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ)))).obj M.val
    { obj := fun X ↦ P.obj X
      map := fun f ↦ P.map f
      map_id := fun X ↦ by ext x; simp; rfl
      map_comp := fun f g ↦ by ext x; simp; rfl }
  property := by
    apply Presheaf.isSheaf_of_isSheaf_comp Y.smallEtaleTopology _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    exact M.isSheaf

set_option backward.isDefEq.respectTransparency false in
private def rowConstantModuleRestrictionFunctor :
    SheafOfModules.{u + 1} (rowConstantModuleRing Y Λ) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj M := rowConstantModuleRestriction Y Λ M
  map f := ObjectProperty.homMk
    { app := fun X ↦ (ModuleCat.restrictScalars
        ((toSheafify Y.smallEtaleTopology
          ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ))).app X).hom).map (f.val.app X)
      naturality := fun {_ _} g ↦ by ext x; exact PresheafOfModules.naturality_apply f.val g x }
  map_id M := by ext X x; rfl
  map_comp f g := by ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
private def rowConstantModuleUnitIso :
    𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ≅
      rowConstantModuleFunctor Y Λ ⋙ rowConstantModuleRestrictionFunctor Y Λ := by
  refine NatIso.ofComponents (fun J ↦ ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun X ↦ ?_) ?_
    · let f := (PresheafOfModules.toSheafify
        (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ)))
        (M₀ := rowConstantModulePresheaf Y Λ J)
        (A := (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J)
        (𝟙 _)).app X
      exact LinearEquiv.toModuleIso (LinearEquiv.ofBijective f.hom
        ⟨fun _ _ h ↦ h, fun x ↦ ⟨x, rfl⟩⟩)
    · intro X Z f
      ext x
      rfl
  · intro J K f
    ext X x
    rfl

set_option backward.isDefEq.respectTransparency false in
private def rowConstantModuleCounitHom
    (M : SheafOfModules.{u + 1} (rowConstantModuleRing Y Λ)) :
    (rowConstantModuleFunctor Y Λ).obj
      ((rowConstantModuleRestrictionFunctor Y Λ).obj M) ⟶ M :=
  (PresheafOfModules.sheafifyHomEquiv
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ)))
    (M₀ := rowConstantModulePresheaf Y Λ (rowConstantModuleRestriction Y Λ M))
    (A := ⟨M.val.presheaf, M.isSheaf⟩)
    (𝟙 _)).symm
      (PresheafOfModules.homMk (𝟙 _) (fun _ _ _ ↦ rfl))

set_option backward.isDefEq.respectTransparency false in
private lemma rowConstantModuleCounitHom_underlying
    (M : SheafOfModules.{u + 1} (rowConstantModuleRing Y Λ)) :
    (PresheafOfModules.toPresheaf _).map (rowConstantModuleCounitHom Y Λ M).val =
      𝟙 M.val.presheaf := by
  have h := PresheafOfModules.comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ)))
    (M₀ := rowConstantModulePresheaf Y Λ (rowConstantModuleRestriction Y Λ M))
    (A := ⟨M.val.presheaf, M.isSheaf⟩)
    (𝟙 _) M.isSheaf (PresheafOfModules.homMk (𝟙 _) (fun _ _ _ ↦ rfl))
  rw [Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private def rowConstantModuleCounitIso :
    rowConstantModuleRestrictionFunctor Y Λ ⋙ rowConstantModuleFunctor Y Λ ≅
      𝟭 (SheafOfModules.{u + 1} (rowConstantModuleRing Y Λ)) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let f := rowConstantModuleCounitHom Y Λ M
    have hf (X : Y.Etaleᵒᵖ) (x : ((rowConstantModuleFunctor Y Λ).obj
        ((rowConstantModuleRestrictionFunctor Y Λ).obj M)).val.obj X) :
        f.val.app X x = x :=
      CategoryTheory.congr_fun
        (NatTrans.congr_app (rowConstantModuleCounitHom_underlying Y Λ M) X) x
    let e : ((rowConstantModuleFunctor Y Λ).obj
        ((rowConstantModuleRestrictionFunctor Y Λ).obj M)).val ≅ M.val :=
      PresheafOfModules.isoMk
      (fun X ↦ LinearEquiv.toModuleIso (LinearEquiv.ofBijective (f.val.app X).hom
        ⟨fun x y h ↦ (hf X x).symm.trans (h.trans (hf X y)),
          fun x ↦ ⟨x, hf X x⟩⟩))
      (fun {_ _} g ↦ f.val.naturality g)
    exact (SheafOfModules.fullyFaithfulForget (rowConstantModuleRing Y Λ)).preimageIso e
  · intro M N f
    apply (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map_injective
    change (PresheafOfModules.toPresheaf _).map
        ((rowConstantModuleFunctor Y Λ).map
          ((rowConstantModuleRestrictionFunctor Y Λ).map f)).val ≫
        (PresheafOfModules.toPresheaf _).map (rowConstantModuleCounitHom Y Λ N).val =
      (PresheafOfModules.toPresheaf _).map (rowConstantModuleCounitHom Y Λ M).val ≫
        (PresheafOfModules.toPresheaf _).map f.val
    rw [rowConstantModuleCounitHom_underlying, rowConstantModuleCounitHom_underlying]
    ext X x
    rfl

private theorem rowConstantModuleFunctor_isEquivalence :
    (rowConstantModuleFunctor Y Λ).IsEquivalence :=
  Functor.IsEquivalence.mk' (rowConstantModuleRestrictionFunctor Y Λ)
    (rowConstantModuleUnitIso Y Λ) (rowConstantModuleCounitIso Y Λ)

end

end ConstantScalars

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

private theorem matching_local_lifting (U : FiniteSplitEtaleHypercover X)
    (n : ℕ) (T : X.Etale)
    (p : ∀ (Δ : SimplexCategory), Δ.len < n →
      (Δ ⟶ SimplexCategory.mk n) → (T ⟶ U.simplicial.obj (op Δ)))
    (hc : ∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
      (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
      p Δ h θ ≫ U.simplicial.map α.op = p Δ' h' (α ≫ θ)) :
    ∃ S : Sieve T, S ∈ X.smallEtaleTopology T ∧
      ∀ (V : X.Etale) (f : V ⟶ T), S f →
        ∃ t : V ⟶ U.simplicial.obj (op (SimplexCategory.mk n)),
          ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
            t ≫ U.simplicial.map θ.op = f ≫ p Δ h θ := by
  obtain ⟨m, hm, _⟩ := U.matching_universal n ((Scheme.Etale.forget X).obj T)
    (fun Δ h θ ↦ (Scheme.Etale.forget X).map (p Δ h θ)) (by
      intro Δ Δ' h h' α θ
      simpa only [← Functor.map_comp] using congrArg (Scheme.Etale.forget X).map
        (hc Δ Δ' h h' α θ))
  let m' : T ⟶ U.matching n := (Scheme.Etale.forget X).preimage m
  have hm' (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n) :
      m' ≫ U.projection n Δ h θ = p Δ h θ := by
    apply (Scheme.Etale.forget X).map_injective
    simpa only [m', Functor.map_comp, Functor.map_preimage] using hm Δ h θ
  let S := Sieve.ofArrows (fun _ : Unit ↦ U.simplicial.obj (op (SimplexCategory.mk n)))
    (fun _ ↦ U.matchingMap n)
  have hS : S ∈ X.smallEtaleTopology (U.matching n) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨y, hy⟩ := (U.matching_cover n).surj x
    exact ⟨(), y, hy⟩
  refine ⟨S.pullback m', X.smallEtaleTopology.pullback_stable m' hS, ?_⟩
  intro V f hf
  obtain ⟨i, t, ht⟩ := Sieve.ofArrows.exists hf
  refine ⟨t, ?_⟩
  intro Δ h θ
  rw [← U.matchingMap_projection n Δ h θ, ← Category.assoc]
  change t ≫ U.matchingMap n ≫ U.projection n Δ h θ = _
  rw [← Category.assoc, ← ht, Category.assoc, hm']

/-- An injective module sheaf has an exact augmented hypercover section complex.
Source: Stacks Project, Hypercoverings, Tag 01GW, for free left modules.
(auxiliary; not a blueprint node).

Proof: realize the sheaf as modules over the sheafified constant ring, without changing
its underlying abelian presheaf. This equivalence preserves injectivity. Enlarge the
hom universe of the etale site and transport its topology and module sheaves along
ULiftHom.equiv. The matching universal property and the surjective matching maps give
local lifts of every lower-simplex matching family. Apply the ringed-hypercover exactness
theorem over this ring sheaf. Transport back the injective augmentation and the exactness
in every positive degree. A single-complex augmentation with these properties is a
quasi-isomorphism, by the degree-zero and positive-degree criteria for homology.
No commutativity of the coefficient ring is used; free modules are left modules. -/
theorem injective_module_row_quasiIso (U : FiniteSplitEtaleHypercover X)
    (R : Type (u + 1)) [Ring R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) [Injective F] :
    QuasiIso (Grothendieck.sectionAugmentation (ModuleCat.{u + 1} R) U F) := by
  let C' := ULiftHom.{u + 1} X.Etale
  let up : X.Etale ⥤ C' := ULiftHom.up
  let down : C' ⥤ X.Etale := ULiftHom.down
  let top' := down.inducedTopology X.smallEtaleTopology
  have : down.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : X.Etale ≌ C').inverse.IsEquivalence)
  have : up.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : X.Etale ≌ C').functor.IsEquivalence)
  have : down.IsContinuous top' X.smallEtaleTopology := by
    dsimp [top', down]
    infer_instance
  have : up.IsContinuous X.smallEtaleTopology top' := by
    exact inferInstanceAs ((ULiftHom.equiv : X.Etale ≌ C').functor.IsContinuous
      X.smallEtaleTopology ((ULiftHom.equiv : X.Etale ≌ C').inverse.inducedTopology
        X.smallEtaleTopology))
  have : (ULiftHom.equiv.symm : C' ≌ X.Etale).functor.IsContinuous top'
      X.smallEtaleTopology := by change down.IsContinuous top' X.smallEtaleTopology; infer_instance
  have : (ULiftHom.equiv.symm : C' ≌ X.Etale).inverse.IsContinuous
      X.smallEtaleTopology top' := by
    change up.IsContinuous X.smallEtaleTopology top'
    infer_instance
  have : HasPullbacks C' := Adjunction.hasLimitsOfShape_of_equivalence down
  let pc := top'.toPrecoverage
  have hpc : pc.toGrothendieck = top' := by
    refine le_antisymm top'.toGrothendieck_toPrecoverage_le ?_
    intro T S hS
    have h := pc.generate_mem_toGrothendieck ((top'.arrows_mem_toPrecoverage_iff S).mpr hS)
    simpa only [Sieve.generate_sieve] using h
  have : top'.Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful down top' X.smallEtaleTopology
  let A := rowConstantModuleRing X R
  let G := rowConstantModuleFunctor X R
  have : G.IsEquivalence := rowConstantModuleFunctor_isEquivalence X R
  let M := G.obj F
  have : Injective M := (G.asEquivalence.map_injective_iff F).mpr inferInstance
  let A' := (down.sheafPushforwardContinuous RingCat.{u + 1}
    top' X.smallEtaleTopology).obj A
  let E : SheafOfModules.{u + 1} A ≌ SheafOfModules.{u + 1} A' :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (ULiftHom.equiv.symm : C' ≌ X.Etale) (𝟙 A') (𝟙 A)
      (by ext V x; change (A.obj.map (𝟙 _)).hom x = x; simp)
      (by ext V x; change (A.obj.map (𝟙 _)).hom x = x; simp)
  let M' : SheafOfModules.{u + 1} A' := E.functor.obj M
  have : Injective M' := (E.map_injective_iff M).mpr inferInstance
  have : pc.toGrothendieck.Subcanonical := by rw [hpc]; infer_instance
  have hseq' := ringedHypercover_injective_augmentation_exact_ring.{u + 1, u + 1, u + 1} pc
  rw [hpc] at hseq'
  have hseq := hseq' A' M' (up.obj (⊤_ X.Etale)) (U.simplicial ⋙ up)
    (Functor.whiskerRight (U.simplicial.augmentOfIsTerminal terminalIsTerminal).hom up) (by
      intro n T w p hp hc
      obtain ⟨S, hS, hlift⟩ := matching_local_lifting U n (down.obj T)
        (fun Δ h θ ↦ down.map (p Δ h θ))
        (fun Δ Δ' h h' α θ ↦ congrArg down.map (hc Δ Δ' h h' α θ))
      refine ⟨S.functorPullback down, ?_, ?_⟩
      · change _ ∈ down.inducedTopology X.smallEtaleTopology T
        rw [← Functor.restrictedTopology_eq_inducedTopology]
        exact Functor.IsCocontinuous.cover_lift hS
      · intro V f hf
        obtain ⟨t, ht⟩ := hlift (down.obj V) (down.map f) hf
        refine ⟨ULift.up t, ?_, fun Δ h θ ↦ congrArg ULift.up (ht Δ h θ)⟩
        apply ULift.ext
        exact terminal.hom_ext _ _)
  let K := (Grothendieck.sectionComplexFunctor (ModuleCat.{u + 1} R) U).obj F
  let a := Grothendieck.sectionAugmentation (ModuleCat.{u + 1} R) U F
  have hd (n : ℕ) (s : K.X n) :
      K.d n (n + 1) s =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • F.obj.map (U.simplicial.δ j).op s := by
    change (((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).obj
      (U.simplicial.rightOp ⋙ F.obj)).d n (n + 1)) s = _
    simp only [AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD]
    change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • F.obj.map (U.simplicial.δ j).op) s = _
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply]
  have hi : Function.Injective (a.f 0) := by
    have h := hseq.1
    change Function.Injective (F.obj.map (terminal.from _).op) at h
    exact h
  have hz : Function.Exact (a.f 0) (K.d 0 1) := by
    have h := hseq.2.1
    change Function.Exact (F.obj.map (terminal.from _).op)
      (fun s ↦ ∑ j : Fin 2, (-1 : ℤ) ^ j.val • F.obj.map (U.simplicial.δ j).op s) at h
    change Function.Exact (F.obj.map (terminal.from _).op) (fun s ↦ K.d 0 1 s)
    simpa only [hd] using h
  have hpos (n : ℕ) : K.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' K n (n + 1) (n + 2) (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    have h := hseq.2.2 n
    change Function.Exact
      (fun s ↦ ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • F.obj.map (U.simplicial.δ j).op s)
      (fun s ↦ ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • F.obj.map (U.simplicial.δ j).op s) at h
    change Function.Exact (fun s ↦ K.d n (n + 1) s) (fun s ↦ K.d (n + 1) (n + 2) s)
    simp only [hd]
    convert h using 1 <;> rfl
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff]
      apply (ShortComplex.quasiIso_iff_of_zeros _ ?_ ?_ ?_).mpr
        ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr hz,
          (ModuleCat.mono_iff_injective _).mpr hi⟩
      · exact HomologicalComplex.single_obj_d (.up ℕ) 0 _ 0 1
      · exact HomologicalComplex.single_obj_d (.up ℕ) 0 _ 0 0
      · exact K.shape 0 0 (by simp)
  | succ n =>
      exact (quasiIsoAt_iff_exactAt a (n + 1)
        (HomologicalComplex.ExactAt.of_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ (n + 1) (by omega)))).mpr (hpos n)

end AlgebraicGeometry.FiniteSplitEtaleHypercover
