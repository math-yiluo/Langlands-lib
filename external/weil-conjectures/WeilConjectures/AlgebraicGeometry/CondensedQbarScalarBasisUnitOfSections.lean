/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasisPushforward
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts

/-! Derived scalar-unit decomposition from coherent coefficient sections.

This is the derived descent part of the scalar-basis construction. -/

@[expose] public section

universe u v w

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

-- Keep the inverse-image and adjunction constructions folded during concrete type checking.
attribute [local irreducible] Mod.derivedExtendMapDerivedCategoryAdjunction
  Adjunction.mapDerivedCategoryAdjunction Mod.extendRestrictAdjunction
  AlgebraicGeometry.ProEtale.upperStarFromPoint AlgebraicGeometry.ProEtale.upperStar
set_option linter.style.haveILetI false

private lemma sigma_desc_comp_sigma_desc
    {C : Type u} [Category.{v} C] {I : Type w} {A B P : C}
    [HasCoproduct (fun _ : I ↦ A)] [HasCoproduct (fun _ : I ↦ B)]
    (e : A ⟶ B) (g : I → (B ⟶ P)) :
    Sigma.desc (fun i ↦ e ≫ Sigma.ι (fun _ : I ↦ B) i) ≫ Sigma.desc g =
      Sigma.desc (fun i ↦ e ≫ g i) := by
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_desc_assoc]
  rw [Category.assoc, Sigma.ι_comp_desc]
  rw [Sigma.ι_comp_desc]

private lemma sigma_desc_comp_map
    {C : Type u} [Category.{v} C] {I : Type w} {A B P : C}
    [HasCoproduct (fun _ : I ↦ A)]
    (f : I → (A ⟶ B)) (m : B ⟶ P) (g : I → (A ⟶ P))
    (h : ∀ i, f i ≫ m = g i) :
    Sigma.desc f ≫ m = Sigma.desc g := by
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, h]

private lemma qbar_scalarUnitLeg_naturality
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    (b : 𝟙_ C ⟶ S) {M N : DerivedCategory (Mod C R)} (f : M ⟶ N) :
    f ≫ Mod.qbar_scalarUnitLeg φ b N = Mod.qbar_scalarUnitLeg φ b M ≫
      (Mod.comap φ).mapDerivedCategory.map ((Mod.extendScalars φ).leftDerivedFunctor.map f) := by
  rw [Mod.qbar_scalarUnitLeg_eq, Mod.qbar_scalarUnitLeg_eq]
  simp only [Category.assoc]
  change (𝟭 (DerivedCategory (Mod C R))).map f ≫
      (Mod.derivedExtendMapDerivedCategoryAdjunction φ).unit.app N ≫ _ = _
  rw [(Mod.derivedExtendMapDerivedCategoryAdjunction φ).unit.naturality_assoc f]
  change (Mod.derivedExtendMapDerivedCategoryAdjunction φ).unit.app M ≫
      (Mod.comap φ).mapDerivedCategory.map ((Mod.extendScalars φ).leftDerivedFunctor.map f) ≫ _ = _
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [(qbar_derivedCenter (Mod.qbar_scalarNatEndo b)).naturality]

private lemma isIso_map_sigma_desc
    {C : Type u} [Category.{v} C] {D : Type*} [Category D]
    {I : Type w} {A B : C} (F : C ⥤ D) (f : I → (A ⟶ B))
    [HasCoproduct (fun _ : I ↦ A)]
    [HasCoproduct (fun _ : I ↦ F.obj A)]
    [PreservesColimit (Discrete.functor (fun _ : I ↦ A)) F]
    [IsIso (Sigma.desc (fun i ↦ F.map (f i)))] :
    IsIso (F.map (Sigma.desc f)) := by
  have : IsIso (sigmaComparison F (fun _ : I ↦ A) ≫ F.map (Sigma.desc f)) := by
    rw [sigmaComparison_map_desc]
    infer_instance
  exact IsIso.of_isIso_comp_left (sigmaComparison F (fun _ : I ↦ A)) _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- Degreewise coproducts and the two derived-functor comparisons need extra elaboration steps.
private lemma qbar_isIso_unit_on_complex
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [PreservesFiniteLimits (Mod.extendScalars φ)]
    {I : Type w} [HasCoproducts.{w} (Mod C R)]
    (b : I → (𝟙_ C ⟶ S))
    (h : ∀ N : Mod C R, IsIso (Sigma.desc (fun i ↦
      (Mod.extendRestrictAdjunction φ).unit.app N ≫
        (Mod.comap φ).map (Mod.qbar_scalarEndo (b i) ((Mod.extendScalars φ).obj N)))))
    (K : CochainComplex (Mod C R) ℤ)
    [HasCoproduct (fun _ : I ↦
      (HomotopyCategory.quotient (Mod C R) (.up ℤ) ⋙ DerivedCategory.Qh).obj K)] :
    IsIso (Sigma.desc (fun i ↦ Mod.qbar_scalarUnitLeg φ (b i)
      ((HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).obj K))) := by
  let Q' := HomotopyCategory.quotient (Mod C R) (.up ℤ) ⋙ DerivedCategory.Qh
  let f (i : I) : K ⟶ ((Mod.comap φ).mapHomologicalComplex _).obj
      (((Mod.extendScalars φ).mapHomologicalComplex _).obj K) :=
    ((Mod.extendRestrictAdjunction φ).mapHomologicalComplex _).unit.app K ≫
    ((Mod.comap φ).mapHomologicalComplex _).map
      ((qbar_complexCenter (Mod.qbar_scalarNatEndo (b i))).app
        (((Mod.extendScalars φ).mapHomologicalComplex _).obj K))
  have hC : IsIso (Sigma.desc f) := by
    have (n : ℤ) : IsIso ((Sigma.desc f).f n) := by
      have hf : (fun i ↦ (HomologicalComplex.eval _ _ n).map (f i)) =
          fun i ↦ (Mod.extendRestrictAdjunction φ).unit.app (K.X n) ≫
            (Mod.comap φ).map
              (Mod.qbar_scalarEndo (b i) ((Mod.extendScalars φ).obj (K.X n))) := by
        funext i
        change (Mod.extendRestrictAdjunction φ).unit.app (K.X n) ≫
          (Mod.comap φ).map
            (((qbar_complexCenter (Mod.qbar_scalarNatEndo (b i))).app
              (((Mod.extendScalars φ).mapHomologicalComplex _).obj K)).f n) = _
        rw [qbar_complexCenter_app_f]
        change (Mod.extendRestrictAdjunction φ).unit.app (K.X n) ≫
          (Mod.comap φ).map ((Mod.qbar_scalarNatEndo (b i)).app
            ((Mod.extendScalars φ).obj (K.X n))) = _
        rw [Mod.qbar_scalarNatEndo_app]
      have : IsIso (Sigma.desc (fun i ↦ (HomologicalComplex.eval _ _ n).map (f i))) := by
        rw [hf]
        exact h (K.X n)
      exact isIso_map_sigma_desc (HomologicalComplex.eval _ _ n) f
    exact HomologicalComplex.Hom.isIso_of_components _
  have hpres : PreservesColimit (Discrete.functor (fun _ : I ↦ K)) DerivedCategory.Q :=
    preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct _)
      ((isColimitMapCoconeCofanMkEquiv _ _ _).symm
        (DerivedCategory.isColimitCofanMkQObj (coproductIsCoproduct _)))
  letI : PreservesColimit (Discrete.functor (fun _ : I ↦ K)) Q' :=
    preservesColimit_of_natIso _ (DerivedCategory.quotientCompQhIso (Mod C R)).symm
  have hmap : IsIso (Sigma.desc (fun i ↦ Q'.map (f i))) := by
    rw [← sigmaComparison_map_desc]
    infer_instance
  let t := (Mod.comap φ).mapDerivedCategory.mapIso
      ((Mod.extendScalars φ).mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≪≫
    (Mod.comap φ).mapDerivedCategoryFactorsh.app _
  have hleg (i : I) :
      (Mod.extendRestrictAdjunction φ).mapDerivedCategoryAdjunction.unit.app
          ((HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).obj K) ≫
        (Mod.comap φ).mapDerivedCategory.map
          ((qbar_derivedCenter (Mod.qbar_scalarNatEndo (b i))).app _) ≫ t.hom =
      Q'.map (f i) := by
    have hfac := (Mod.extendRestrictAdjunction φ).mapDerivedCategoryAdjunction_unit_app_fac
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hfac
    have e₁ := (qbar_derivedCenter (Mod.qbar_scalarNatEndo (b i))).naturality
      ((Mod.extendScalars φ).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K))
    dsimp only [CategoryTheory.Functor.comp_obj] at e₁
    rw [qbar_derivedCenter_Qh] at e₁
    have e₂ := (Mod.comap φ).mapDerivedCategoryFactorsh.hom.naturality
      ((qbar_homotopyCenter (Mod.qbar_scalarNatEndo (b i))).app
        (((Mod.extendScalars φ).mapHomotopyCategory _).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj K)))
    simp only [CategoryTheory.Functor.comp_map] at e₂
    dsimp only [t, Q', Functor.comp_obj, Functor.comp_map]
    simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.app_hom]
    rw [← (Mod.comap φ).mapDerivedCategory.map_comp_assoc, ← e₁,
      (Mod.comap φ).mapDerivedCategory.map_comp_assoc]
    rw [e₂, reassoc_of% hfac]
    dsimp only [f, Q', CategoryTheory.Functor.comp_map]
    rw [qbar_homotopyCenter_app]
    rw [Functor.mapHomotopyCategory_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    simp only [Functor.mapHomotopyCategory_obj, HomotopyCategory.quotient_obj_as]
  have hd : IsIso (Sigma.desc (f := fun _ : I ↦ Q'.obj K) (fun i : I ↦
      (Mod.extendRestrictAdjunction φ).mapDerivedCategoryAdjunction.unit.app
          ((HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).obj K) ≫
        (Mod.comap φ).mapDerivedCategory.map
          ((qbar_derivedCenter (Mod.qbar_scalarNatEndo (b i))).app _))) := by
    have hdesc := sigma_desc_comp_map (A := Q'.obj K) _ t.hom _
      (fun i ↦ (Category.assoc _ _ _).trans (hleg i))
    have : IsIso (Sigma.desc (f := fun _ : I ↦ Q'.obj K) (fun i : I ↦
        (Mod.extendRestrictAdjunction φ).mapDerivedCategoryAdjunction.unit.app
            ((HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).obj K) ≫
          (Mod.comap φ).mapDerivedCategory.map
            ((qbar_derivedCenter (Mod.qbar_scalarNatEndo (b i))).app _)) ≫ t.hom) := by
      exact hdesc.symm ▸ hmap
    exact IsIso.of_isIso_comp_right _ t.hom
  let c := (Mod.comap φ).mapDerivedCategory.mapIso
    ((Mod.extendScalars φ).leftDerivedFunctorIsoMapDerivedCategory.app
      ((HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).obj K))
  have hc (i : I) : Mod.qbar_scalarUnitLeg φ (b i)
      ((HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).obj K) ≫ c.hom =
      (Mod.extendRestrictAdjunction φ).mapDerivedCategoryAdjunction.unit.app
          ((HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).obj K) ≫
        (Mod.comap φ).mapDerivedCategory.map
          ((qbar_derivedCenter (Mod.qbar_scalarNatEndo (b i))).app _) := by
    rw [Mod.qbar_scalarUnitLeg_eq]
    dsimp only [c]
    simp only [CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Category.assoc,
      ← (Mod.comap φ).mapDerivedCategory.map_comp]
    rw [← (qbar_derivedCenter (Mod.qbar_scalarNatEndo (b i))).naturality]
    rw [(Mod.comap φ).mapDerivedCategory.map_comp]
    rw [← Category.assoc]
    congr 1
    simp only [Mod.derivedExtendMapDerivedCategoryAdjunction,
      Mod.derivedExtendRestrictAdjunction, Mod.rightDerivedComapIsoMapDerivedCategory,
      Adjunction.mapDerivedCategoryAdjunction, Adjunction.ofNatIsoLeft_unit,
      Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.whiskerLeft_app,
      Category.assoc]
    rw [← (Mod.comap φ).rightDerivedFunctorIsoMapDerivedCategory.hom.naturality]
  have : IsIso (Sigma.desc (fun i : I ↦
      Mod.qbar_scalarUnitLeg φ (b i)
        ((HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).obj K)) ≫ c.hom) := by
    rw [sigma_desc_comp_map _ c.hom _ hc]
    exact hd
  exact IsIso.of_isIso_comp_right _ c.hom

-- Transport is generic so the sheaf inverse-image definitions stay folded at the call site.
private lemma qbar_isIso_unit
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [PreservesFiniteLimits (Mod.extendScalars φ)]
    {I : Type w} [HasCoproducts.{w} (Mod C R)]
    (b : I → (𝟙_ C ⟶ S))
    (h : ∀ N : Mod C R, IsIso (Sigma.desc (fun i ↦
      (Mod.extendRestrictAdjunction φ).unit.app N ≫
        (Mod.comap φ).map (Mod.qbar_scalarEndo (b i) ((Mod.extendScalars φ).obj N)))))
    (M : DerivedCategory (Mod C R)) [HasCoproduct (fun _ : I ↦ M)] :
    IsIso (Sigma.desc (fun i ↦ Mod.qbar_scalarUnitLeg φ (b i) M)) := by
  classical
  obtain ⟨K, _, ⟨e₀⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  let QK := (HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).obj K
  let e := e₀ ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app K
  letI : HasCoproduct (fun _ : I ↦ QK) :=
    hasCoproduct_of_equiv_of_iso (fun _ : I ↦ M)
      (fun _ : I ↦ QK) (Equiv.refl I) (fun _ ↦ e.symm)
  let u (N : DerivedCategory (Mod C R)) (i : I) :=
    Mod.qbar_scalarUnitLeg φ (b i) N
  let s : (∐ (fun _ : I ↦ QK)) ⟶
      (∐ (fun _ : I ↦ M)) :=
    Sigma.desc (fun i ↦ e.inv ≫ Sigma.ι (fun _ : I ↦ M) i)
  let sInv : (∐ (fun _ : I ↦ M)) ⟶
      (∐ (fun _ : I ↦ QK)) :=
    Sigma.desc (fun i ↦ e.hom ≫ Sigma.ι (fun _ : I ↦ QK) i)
  have hs : IsIso s := by
    refine ⟨⟨sInv, ?_, ?_⟩⟩
    · apply Sigma.hom_ext
      intro i
      simp [s, sInv, Category.assoc]
    · apply Sigma.hom_ext
      intro i
      simp [s, sInv, Category.assoc]
  have he : ∀ i : I, e.inv ≫ u M i = u QK i ≫
      (Mod.comap φ).mapDerivedCategory.map
        ((Mod.extendScalars φ).leftDerivedFunctor.map e.inv) := by
    intro i
    exact qbar_scalarUnitLeg_naturality φ (b i) e.inv
  have hdesc :
      Sigma.desc (fun i : I ↦ u QK i) ≫
          (Mod.comap φ).mapDerivedCategory.map
            ((Mod.extendScalars φ).leftDerivedFunctor.map e.inv) =
        s ≫ Sigma.desc (fun i : I ↦ u M i) := by
    have hsdesc : s ≫ Sigma.desc (fun i : I ↦ u M i) =
        Sigma.desc (fun i : I ↦ e.inv ≫ u M i) := by
      exact sigma_desc_comp_sigma_desc e.inv (u M)
    exact (sigma_desc_comp_map
      (fun i ↦ u QK i)
      ((Mod.comap φ).mapDerivedCategory.map
        ((Mod.extendScalars φ).leftDerivedFunctor.map e.inv))
      (fun i ↦ e.inv ≫ u M i) (fun i ↦ (he i).symm)).trans hsdesc.symm
  have hQ' := qbar_isIso_unit_on_complex φ b h K
  have hcomp : IsIso (Sigma.desc (fun i : I ↦ u QK i) ≫
      (Mod.comap φ).mapDerivedCategory.map
        ((Mod.extendScalars φ).leftDerivedFunctor.map e.inv)) := by
    letI := hQ'
    infer_instance
  rw [hdesc] at hcomp
  letI := hs
  letI := hcomp
  exact IsIso.of_isIso_comp_left s _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- An ordinary scalar-unit copower for an exact extension descends to derived objects.
Source: Compatibility.lean, `isIso_derivedBasisUnitDesc` and
`isIso_leftDerivedBasisUnitDesc`, with coproducts replacing finite biproducts.

Proof: evaluate the scalar-unit map of complexes in each degree. The ordinary module
hypothesis and the coproduct comparison for evaluation make it invertible. Localization
preserves this coproduct by `DerivedCategory.isColimitCofanMkQObj`. The factorization
isomorphisms for exact functors and the adjunction-unit factorization identify its localized
legs with the termwise derived unit and localized central actions. The comparison from left
derived extension to exact derived extension respects these legs by central naturality.
Finally represent an arbitrary derived object by a complex and transport the copower and
its scalar legs along the representative isomorphism. Coefficient-section coherence is
unnecessary for this descent; the outer theorem retains it separately.
(auxiliary; not a blueprint node) -/
theorem condensedQbar_scalar_basis_unit_of_sections
    (I : Type (u + 1))
    (b : ∀ Z : Scheme.{u}, I →
      (𝟙_ (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) ⟶
        condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z))
    (hexact : ∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)))
    (h : ∀ (Z : Scheme.{u})
      (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) Z))
      [HasCoproduct (fun _ : I ↦ N)],
      IsIso (Sigma.desc (f := fun _ : I ↦ N) fun i ↦
        (Mod.extendRestrictAdjunction (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).unit.app N ≫
        (Mod.comap (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).map
          (Mod.qbar_scalarEndo (b Z i) ((Mod.extendScalars (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).obj N)))) :
    ∀ (Z : Scheme.{u}) (M : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) Z)))
      [HasCoproduct (fun _ : I ↦ M)],
      IsIso (Sigma.desc (f := fun _ : I ↦ M) fun i ↦
        Mod.qbar_scalarUnitLeg (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z) (b Z i) M) := by
  intro Z M hM
  let A := Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj E) Z)
  letI : HasCoproducts.{u + 1} A := fun J ↦
    HasColimitsOfShape.of_small.{u + 1, u + 1} A (Discrete J)
  letI := hexact Z
  exact qbar_isIso_unit _ (b Z) (fun N ↦ h Z N) M

end AlgebraicGeometry.ProEtale.CondensedRing
