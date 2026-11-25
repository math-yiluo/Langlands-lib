/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison

import WeilConjectures.AlgebraicGeometry.Flat.FlatModel
import WeilConjectures.AlgebraicGeometry.SixFunctors.SiteHomComparisonThick
import all WeilConjectures.AlgebraicGeometry.Lisse.LisseFlatHomSiteComparison
import all WeilConjectures.AlgebraicGeometry.StratumHomComparisonMate.StratumHomComparisonMate
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDualityClosedComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.SixFunctors.Etale.EtaleGeometricBiduality
import all WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport

/-! # Finite-stage duality under the site comparison

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
proposition-six-operations-dctf--15, order 2084
(blueprint: proposition-six-operations-dctf--15).

The comparison is the evaluation-defined arrow. The dualizing object on the
pro-etale site is the transported etale exceptional functor applied to the unit.
The equations below specify preservation of evaluation and its transpose.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u v w c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry

namespace CategoryTheory

/-- Transport a specified degree-zero map through an exact functor and specified
identifications of the degree-zero source and target. This packages only composition
of the existing canonical comparisons.
Source: blueprint order 2084, proof step 9
(blueprint: proposition-six-operations-dctf--15). -/
noncomputable def finiteDualitySingleTransport
    {C : Type c} [Category.{v} C] [Abelian C] [HasDerivedCategory.{v} C]
    {D : Type d} [Category.{w} D] [Abelian D] [HasDerivedCategory.{w} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {V : C} {V' : D} (ε : F.obj V ⟶ V')
    {U : DerivedCategory C} {U' : DerivedCategory D}
    (i : (DerivedCategory.singleFunctor C 0).obj V ≅ U)
    (j : (DerivedCategory.singleFunctor D 0).obj V' ≅ U') :
    F.mapDerivedCategory.obj U ⟶ U' :=
  F.mapDerivedCategory.map i.inv ≫
    (F.mapDerivedCategorySingleFunctor 0).hom.app V ≫
    (DerivedCategory.singleFunctor D 0).map ε ≫ j.hom

section HomComparison
open MonoidalClosed
variable {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  {D : Type d} [Category.{w} D] [MonoidalCategory D] [MonoidalClosed D]
  (F : C ⥤ D) [F.Monoidal] (R : D ⥤ C) (adj : F ⊣ R)

private noncomputable def comparisonTensor (K : C) :
    tensorLeft K ⋙ F ≅ F ⋙ tensorLeft (F.obj K) :=
  NatIso.ofComponents (fun T ↦ (Functor.Monoidal.μIso F K T).symm)
    (fun f ↦ (Functor.OplaxMonoidal.δ_natural_right F K f).symm)

private noncomputable def comparisonHomAdjunction (K : C) :
    tensorLeft K ⋙ F ⊣ ihom (F.obj K) ⋙ R :=
  (adj.comp (ihom.adjunction (F.obj K))).ofNatIsoLeft (comparisonTensor F K).symm

private noncomputable def comparisonHomProjection (K : C) :
    R ⋙ ihom K ≅ ihom (F.obj K) ⋙ R :=
  ((ihom.adjunction K).comp adj).rightAdjointUniq (comparisonHomAdjunction F R adj K)

private theorem comparisonHomProjection_transpose (K : C) {T : C} {N : D}
    (f : T ⟶ (ihom K).obj (R.obj N)) :
    ((comparisonHomAdjunction F R adj K).homEquiv _ _).symm
      (f ≫ (comparisonHomProjection F R adj K).hom.app N) =
    (((ihom.adjunction K).comp adj).homEquiv _ _).symm f := by
  rw [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  dsimp only [comparisonHomProjection]
  rw [Adjunction.rightAdjointUniq_hom_app_counit]
  rfl

private theorem comparisonHom_unit (K M : C) :
    adj.unit.app ((ihom K).obj M) ≫
      R.map ((Functor.LaxMonoidal.ihomComparison F K).app M) =
    (ihom K).map (adj.unit.app M) ≫
      (comparisonHomProjection F R adj K).hom.app (F.obj M) := by
  apply ((comparisonHomAdjunction F R adj K).homEquiv _ _).symm.injective
  rw [comparisonHomProjection_transpose]
  change ((comparisonHomAdjunction F R adj K).homEquiv _ _).symm
      (adj.homEquiv _ _ ((Functor.LaxMonoidal.ihomComparison F K).app M)) = _
  simp only [comparisonHomAdjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
    Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  rw [Equiv.symm_apply_apply]
  change Functor.OplaxMonoidal.δ F K ((ihom K).obj M) ≫
      uncurry ((Functor.LaxMonoidal.ihomComparison F K).app M) =
    (adj.homEquiv _ _).symm (uncurry ((ihom K).map (adj.unit.app M)))
  rw [show (ihom K).map (adj.unit.app M) =
    𝟙 _ ≫ (ihom K).map (adj.unit.app M) by simp,
    uncurry_natural_right, uncurry_id_eq_ev]
  rw [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  erw [adj.left_triangle_components, Category.comp_id]
  rw [uncurry_eq, Functor.LaxMonoidal.ihomComparison_ev]
  rw [Functor.Monoidal.δ_μ_assoc]
  rfl

private theorem isIso_comparisonHom
    (K M : C) [IsIso (adj.unit.app M)]
    [IsIso (adj.unit.app ((ihom K).obj M))]
    (h : Nonempty (F.obj ((ihom K).obj M) ≅ (ihom (F.obj K)).obj (F.obj M))) :
    IsIso ((Functor.LaxMonoidal.ihomComparison F K).app M) := by
  let b := (Functor.LaxMonoidal.ihomComparison F K).app M
  have hr : IsIso (R.map b) := by
    have : IsIso (adj.unit.app ((ihom K).obj M) ≫ R.map b) := by
      rw [comparisonHom_unit F R adj K M]
      infer_instance
    exact IsIso.of_isIso_comp_left (adj.unit.app ((ihom K).obj M)) _
  have hcu : IsIso (adj.counit.app (F.obj ((ihom K).obj M))) := by
    have : IsIso (F.map (adj.unit.app ((ihom K).obj M)) ≫ adj.counit.app _) := by
      erw [adj.left_triangle_components]
      infer_instance
    exact IsIso.of_isIso_comp_left (F.map (adj.unit.app ((ihom K).obj M))) _
  obtain ⟨e⟩ := h
  have hct : IsIso (adj.counit.app ((ihom (F.obj K)).obj (F.obj M))) := by
    have : IsIso ((R ⋙ F).map e.hom ≫ adj.counit.app _) := by
      rw [adj.counit.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left ((R ⋙ F).map e.hom) _
  have : IsIso (adj.counit.app (F.obj ((ihom K).obj M)) ≫ b) := by
    erw [← adj.counit.naturality b]
    change IsIso (F.map (R.map b) ≫
      adj.counit.app ((ihom (F.obj K)).obj (F.obj M)))
    infer_instance
  exact IsIso.of_isIso_comp_left (adj.counit.app (F.obj ((ihom K).obj M))) b

end HomComparison

private theorem transported_braiding
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [BraidedCategory D]
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (e : F ≅ G)
    (hδ : ∀ K M, Functor.OplaxMonoidal.δ G K M =
      e.inv.app (K ⊗ M) ≫ Functor.OplaxMonoidal.δ F K M ≫
        (e.hom.app K ⊗ₘ e.hom.app M))
    (hF : ∀ K M, F.map (β_ K M).hom ≫ Functor.OplaxMonoidal.δ F M K =
      Functor.OplaxMonoidal.δ F K M ≫ (β_ (F.obj K) (F.obj M)).hom) (K M : C) :
    G.map (β_ K M).hom ≫ Functor.OplaxMonoidal.δ G M K =
      Functor.OplaxMonoidal.δ G K M ≫ (β_ (G.obj K) (G.obj M)).hom := by
  rw [hδ, hδ, e.inv.naturality_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% (hF K M), ← BraidedCategory.braiding_naturality]

private theorem native_braiding
    {C : Type c} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasDerivedCategory.{w} C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C] (K L : DerivedCategory C) :
    let := DerivedCategory.symmetricCategory C
    HEq (DerivedMonoidal.braiding' DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) K L).hom (β_ K L).hom := by
  rfl

private theorem native_toIhomIhom
    {C : Type c} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasDerivedCategory.{w} C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C] (W K : DerivedCategory C) :
    @MonoidalClosed.toIhomIhom _ _ _ (DerivedCategory.braidedCategory' C) _ W K =
      @MonoidalClosed.toIhomIhom _ _ _
        (DerivedCategory.symmetricCategory C).toBraidedCategory _ W K := by
  rfl

private theorem normalized_pairing
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    [SymmetricCategory C] (W : C)
    (b : curriedTensor C ≅ (curriedTensor C).flip)
    (hb : ∀ K L : C, HEq ((b.hom.app K).app L) (β_ K L).hom)
    (e : ∀ K : C, (ihom K).obj W ⊗ K ⟶ W)
    (he : ∀ K : C, (ihom.adjunction K).homEquiv _ W
      ((b.hom.app K).app ((ihom K).obj W) ≫ e K) = 𝟙 _)
    (δ : ∀ K : C, K ⟶ (ihom ((ihom K).obj W)).obj W)
    (hδ : ∀ K, δ K = (ihom.adjunction
      ((ihom K).obj W)).homEquiv K W (e K)) (K : C) :
    e K = (β_ ((ihom K).obj W) K).hom ≫
        (ihom.ev K).app W ∧
      δ K = MonoidalClosed.toIhomIhom W K := by
  have h : e K = (β_ ((ihom K).obj W) K).hom ≫
      (ihom.ev K).app W := by
    apply (cancel_epi (β_ K ((ihom K).obj W)).hom).mp
    have heK := congrArg ((ihom.adjunction K).homEquiv _ W).symm (he K)
    rw [eq_of_heq (hb K ((ihom K).obj W))] at heK
    simpa only [Equiv.symm_apply_apply, MonoidalClosed.homEquiv_symm_apply_eq,
      MonoidalClosed.uncurry_id_eq_ev, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp] using heK
  exact ⟨h, by rw [hδ K, h]; rfl⟩

private theorem normalized_pairing_choice
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    [SymmetricCategory C] (W : C)
    (P : (curriedTensor C ≅ (curriedTensor C).flip) → Prop)
    (Q : (∀ K : C, (MonoidalClosed.internalHom.obj (op K)).obj W ⊗ K ⟶ W) →
      (∀ K : C, K ⟶ (dualityDoubleFunctor MonoidalClosed.internalHom W).obj K) → Prop)
    (h : ∃ b : curriedTensor C ≅ (curriedTensor C).flip, P b ∧
      ∃ e : ∀ K : C, (MonoidalClosed.internalHom.obj (op K)).obj W ⊗ K ⟶ W,
        (∀ K : C, (MonoidalClosed.internalHomAdjunction₂.adj K).homEquiv _ W
          ((b.hom.app K).app ((MonoidalClosed.internalHom.obj (op K)).obj W) ≫ e K) = 𝟙 _) ∧
        ∃ δ : ∀ K : C, K ⟶ (dualityDoubleFunctor MonoidalClosed.internalHom W).obj K,
          (∀ K, δ K = (MonoidalClosed.internalHomAdjunction₂.adj
            ((MonoidalClosed.internalHom.obj (op K)).obj W)).homEquiv K W (e K)) ∧ Q e δ)
    (hb : ∀ b, P b → ∀ K L : C, HEq ((b.hom.app K).app L) (β_ K L).hom)
    (K : C) :
    h.choose_spec.2.choose K =
        (β_ ((MonoidalClosed.internalHom.obj (op K)).obj W) K).hom ≫ (ihom.ev K).app W ∧
      h.choose_spec.2.choose_spec.2.choose K = MonoidalClosed.toIhomIhom W K :=
  normalized_pairing W h.choose (hb _ h.choose_spec.1) h.choose_spec.2.choose
    h.choose_spec.2.choose_spec.1 h.choose_spec.2.choose_spec.2.choose
    h.choose_spec.2.choose_spec.2.choose_spec.1 K

private theorem comparisonData_native
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    [SymmetricCategory C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [MonoidalClosed D]
    [SymmetricCategory D] (F : C ⥤ D) [F.Braided]
    {W : C} {W' : D} (ω : F.obj W ≅ W')
    (P : ObjectProperty C) (P' : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [P'.IsClosedUnderIsomorphisms]
    (hD : ∀ K, P K → P ((ihom K).obj W))
    (hδ : ∀ K, P K → IsIso (MonoidalClosed.toIhomIhom W K))
    (hβ : ∀ K, P K →
      IsIso ((Functor.LaxMonoidal.ihomComparison F K).app W))
    (eC : ∀ K : C, (ihom K).obj W ⊗ K ⟶ W)
    (eD : ∀ K : D, (ihom K).obj W' ⊗ K ⟶ W')
    (δC : ∀ K : C, K ⟶ (ihom ((ihom K).obj W)).obj W)
    (δD : ∀ K : D, K ⟶ (ihom ((ihom K).obj W')).obj W')
    (heC : ∀ K, eC K = (β_ ((ihom K).obj W) K).hom ≫ (ihom.ev K).app W)
    (heD : ∀ K, eD K = (β_ ((ihom K).obj W') K).hom ≫ (ihom.ev K).app W')
    (hδC : ∀ K, δC K = MonoidalClosed.toIhomIhom W K)
    (hδD : ∀ K, δD K = MonoidalClosed.toIhomIhom W' K)
    (e : P.FullSubcategory ≌ P'.FullSubcategory)
    (he : e.functor ⋙ P'.ι ≅ P.ι ⋙ F) :
    (∀ K, P K → ∃ cK : F.obj ((ihom K).obj W) ≅ (ihom (F.obj K)).obj W',
      cK.hom = (Functor.LaxMonoidal.ihomComparison F K).app W ≫
        (ihom (F.obj K)).map ω.hom ∧
      ∃ cDK : F.obj ((ihom ((ihom K).obj W)).obj W) ≅
          (ihom (F.obj ((ihom K).obj W))).obj W',
        cDK.hom = (Functor.LaxMonoidal.ihomComparison F ((ihom K).obj W)).app W ≫
          (ihom (F.obj ((ihom K).obj W))).map ω.hom ∧
        (cK.hom ▷ F.obj K) ≫ eD (F.obj K) =
          Functor.LaxMonoidal.μ F ((ihom K).obj W) K ≫ F.map (eC K) ≫ ω.hom ∧
        F.map (δC K) ≫ cDK.hom ≫ (MonoidalClosed.pre cK.inv).app W' = δD (F.obj K)) ∧
      (∃ d : P'.FullSubcategoryᵒᵖ ≌ P'.FullSubcategory,
        Nonempty (d.functor ⋙ P'.ι ≅ P'.ι.op ⋙ MonoidalClosed.internalHom.flip.obj W')) ∧
      ∀ K, P' K → IsIso (δD K) := by
  classical
  have hF (K : C) (hK : P K) : P' (F.obj K) :=
    P'.prop_of_iso (he.app ⟨K, hK⟩) (e.functor.obj ⟨K, hK⟩).property
  let J := P'.lift (P.ι ⋙ F) (fun K ↦ hF K.obj K.property)
  have : J.IsEquivalence := Functor.isEquivalence_of_iso
    ((P'.fullyFaithfulι.whiskeringRight _).preimageIso he)
  obtain ⟨hD', _, hcomp, htransport⟩ :=
    MonoidalClosed.evaluationBidualComparisonTransport F ω P P' hD hF hβ
  have hsource : (P.liftDual (MonoidalClosed.internalHom.flip.obj W) hD).IsEquivalence :=
    (P.liftDualEquivalence (MonoidalClosed.internalHom.flip.obj W) hD
      (MonoidalClosed.toIhomIhomNatTrans W) hδ).isEquivalence_functor
  obtain ⟨_, hδ'⟩ := htransport hsource hδ
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    let cK := MonoidalClosed.evaluationDualComparison F ω K (hβ K hK)
    let cDK := MonoidalClosed.evaluationDualComparison F ω
      ((ihom K).obj W) (hβ _ (hD K hK))
    refine ⟨cK, rfl, cDK, rfl, ?_, ?_⟩
    · have h := (congrArg (fun f ↦ (cK.hom ⊗ₘ 𝟙 (F.obj K)) ≫ f) (heD (F.obj K))).trans
        ((hcomp K hK).1.trans (congrArg
          (fun f ↦ Functor.LaxMonoidal.μ F ((ihom K).obj W) K ≫ F.map f ≫ ω.hom)
          (heC K).symm))
      simpa only [tensorHom_id] using h
    · exact (congrArg (fun f ↦ F.map f ≫ cDK.hom ≫
        (MonoidalClosed.pre cK.inv).app W') (hδC K)).trans
        ((hcomp K hK).2.symm.trans (hδD (F.obj K)).symm)
  · exact ⟨P'.liftDualEquivalence (MonoidalClosed.internalHom.flip.obj W') hD'
      (MonoidalClosed.toIhomIhomNatTrans W') hδ', ⟨Iso.refl _⟩⟩
  · intro K hK
    exact (hδD K).symm ▸ hδ' K hK

/-- The evaluation and biduality equations for specified Hom and tensor comparisons. -/
noncomputable def evaluationDualityCompatibility
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
    (F : C ⥤ D) (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (b : ∀ K M, F.obj ((HC.obj (op K)).obj M) ⟶
      (HD.obj (op (F.obj K))).obj (F.obj M))
    (t : ∀ K M, (TD.obj (F.obj K)).obj (F.obj M) ⟶ F.obj ((TC.obj K).obj M))
    {W : C} {W' : D} (ω : F.obj W ≅ W')
    (eC : ∀ K, (TC.obj ((HC.obj (op K)).obj W)).obj K ⟶ W)
    (eD : ∀ K, (TD.obj ((HD.obj (op K)).obj W')).obj K ⟶ W')
    (δC : ∀ K, K ⟶ (dualityDoubleFunctor HC W).obj K)
    (δD : ∀ K, K ⟶ (dualityDoubleFunctor HD W').obj K) (K : C) : Prop :=
  ∃ cK : F.obj ((HC.obj (op K)).obj W) ≅
        (HD.obj (op (F.obj K))).obj W',
      cK.hom = b K W ≫ (HD.obj (op (F.obj K))).map ω.hom ∧
      ∃ cDK : F.obj ((HC.obj (op ((HC.obj (op K)).obj W))).obj W) ≅
          (HD.obj (op (F.obj ((HC.obj (op K)).obj W)))).obj W',
        cDK.hom = b ((HC.obj (op K)).obj W) W ≫
          (HD.obj (op (F.obj ((HC.obj (op K)).obj W)))).map ω.hom ∧
        (TD.map cK.hom).app (F.obj K) ≫ eD (F.obj K) =
          t ((HC.obj (op K)).obj W) K ≫ F.map (eC K) ≫ ω.hom ∧
        F.map (δC K) ≫ cDK.hom ≫ (HD.map cK.inv.op).app W' = δD (F.obj K)

/-- The evaluation and biduality equations for specified Hom and tensor comparisons. -/
noncomputable def evaluationDualityConclusions
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
    (F : C ⥤ D) (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (b : ∀ K M, F.obj ((HC.obj (op K)).obj M) ⟶
      (HD.obj (op (F.obj K))).obj (F.obj M))
    (t : ∀ K M, (TD.obj (F.obj K)).obj (F.obj M) ⟶ F.obj ((TC.obj K).obj M))
    {W : C} {W' : D} (ω : F.obj W ≅ W')
    (eC : ∀ K, (TC.obj ((HC.obj (op K)).obj W)).obj K ⟶ W)
    (eD : ∀ K, (TD.obj ((HD.obj (op K)).obj W')).obj K ⟶ W')
    (δC : ∀ K, K ⟶ (dualityDoubleFunctor HC W).obj K)
    (δD : ∀ K, K ⟶ (dualityDoubleFunctor HD W').obj K)
    (P : ObjectProperty C) (P' : ObjectProperty D) : Prop :=
  (∀ K, P K → evaluationDualityCompatibility F HC HD TC TD b t ω eC eD δC δD K) ∧
  (∃ e : P.FullSubcategory ≌ P'.FullSubcategory,
    Nonempty (e.functor ⋙ P'.ι ≅ P.ι ⋙ F)) ∧
  (∃ d : P'.FullSubcategoryᵒᵖ ≌ P'.FullSubcategory,
    Nonempty (d.functor ⋙ P'.ι ≅ P'.ι.op ⋙ HD.flip.obj W')) ∧
  ∀ K, P' K → IsIso (δD K)

/-- Complete duality comparison data, parameterized by the two normalized pairing predicates.
Source: blueprint order 2084 (blueprint: proposition-six-operations-dctf--15). -/
structure EvaluationDualityData
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
    (F : C ⥤ D) (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (b : ∀ K M, F.obj ((HC.obj (op K)).obj M) ⟶
      (HD.obj (op (F.obj K))).obj (F.obj M))
    (t : ∀ K M, (TD.obj (F.obj K)).obj (F.obj M) ⟶ F.obj ((TC.obj K).obj M))
    (EC : C → Prop) (ED : D → Prop)
    (eC : ∀ W, EC W → ∀ K, (TC.obj ((HC.obj (op K)).obj W)).obj K ⟶ W)
    (eD : ∀ W, ED W → ∀ K, (TD.obj ((HD.obj (op K)).obj W)).obj K ⟶ W)
    (δC : ∀ W, EC W → ∀ K, K ⟶ (dualityDoubleFunctor HC W).obj K)
    (δD : ∀ W, ED W → ∀ K, K ⟶ (dualityDoubleFunctor HD W).obj K)
    (W : C) (W' : D) (w : F.obj W ⟶ W')
    (P Q : ObjectProperty C) (P' : ObjectProperty D) : Prop where
  homComparison : ∀ K M, P K → Q M → IsIso (b K M)
  transport : ∃ ω : F.obj W ≅ W', ω.hom = w ∧ ∃ hC : EC W, ∃ hD : ED W',
    evaluationDualityConclusions F HC HD TC TD b t ω (eC W hC) (eD W' hD)
      (δC W hC) (δD W' hD) P P'

private theorem comparisonData_raw
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    [SymmetricCategory C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [MonoidalClosed D]
    [SymmetricCategory D] (F : C ⥤ D) [F.Braided]
    (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (hHC : HC = MonoidalClosed.internalHom) (hHD : HD = MonoidalClosed.internalHom)
    (hTC : TC = curriedTensor C) (hTD : TD = curriedTensor D)
    (b : ∀ K M, F.obj ((HC.obj (op K)).obj M) ⟶
      (HD.obj (op (F.obj K))).obj (F.obj M))
    (hb : HEq b (fun K M ↦
      (Functor.LaxMonoidal.ihomComparison F K).app M))
    (t : ∀ K M, (TD.obj (F.obj K)).obj (F.obj M) ⟶ F.obj ((TC.obj K).obj M))
    (ht : HEq t (fun K M ↦ Functor.LaxMonoidal.μ F K M))
    {W : C} {W' : D} (ω : F.obj W ≅ W')
    (P : ObjectProperty C) (P' : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [P'.IsClosedUnderIsomorphisms]
    (hD : ∀ K, P K → P ((HC.obj (op K)).obj W))
    (hβ : ∀ K, P K → IsIso (b K W))
    (eC : ∀ K, (TC.obj ((HC.obj (op K)).obj W)).obj K ⟶ W)
    (eD : ∀ K, (TD.obj ((HD.obj (op K)).obj W')).obj K ⟶ W')
    (δC : ∀ K, K ⟶ (dualityDoubleFunctor HC W).obj K)
    (δD : ∀ K, K ⟶ (dualityDoubleFunctor HD W').obj K)
    (heC : HEq eC (fun K ↦ (β_ ((ihom K).obj W) K).hom ≫ (ihom.ev K).app W))
    (heD : HEq eD (fun K ↦ (β_ ((ihom K).obj W') K).hom ≫ (ihom.ev K).app W'))
    (hδC : HEq δC (fun K ↦ MonoidalClosed.toIhomIhom W K))
    (hδD : HEq δD (fun K ↦ MonoidalClosed.toIhomIhom W' K))
    (hδ : ∀ K, P K → IsIso (δC K))
    (e : P.FullSubcategory ≌ P'.FullSubcategory)
    (he : e.functor ⋙ P'.ι ≅ P.ι ⋙ F) :
    (∀ K, P K → evaluationDualityCompatibility F HC HD TC TD b t ω eC eD δC δD K) ∧
      (∃ d : P'.FullSubcategoryᵒᵖ ≌ P'.FullSubcategory,
        Nonempty (d.functor ⋙ P'.ι ≅ P'.ι.op ⋙ HD.flip.obj W')) ∧
      ∀ K, P' K → IsIso (δD K) := by
  subst HC
  subst HD
  subst TC
  subst TD
  have hb' := eq_of_heq hb
  subst b
  have ht' := eq_of_heq ht
  subst t
  have hδC' := eq_of_heq hδC
  rw [hδC'] at hδ
  exact comparisonData_native F ω P P' hD hδ hβ eC eD δC δD
    (fun K ↦ congrFun (eq_of_heq heC) K)
    (fun K ↦ congrFun (eq_of_heq heD) K)
    (fun K ↦ congrFun (eq_of_heq hδC) K)
    (fun K ↦ congrFun (eq_of_heq hδD) K) e he

private theorem comparisonData_allPairings
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    [SymmetricCategory C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [MonoidalClosed D]
    [SymmetricCategory D] (F : C ⥤ D) [F.Monoidal]
    (hbraiding : ∀ K L, Functor.LaxMonoidal.μ F K L ≫ F.map (β_ K L).hom =
      (β_ (F.obj K) (F.obj L)).hom ≫ Functor.LaxMonoidal.μ F L K)
    (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (hHC : HC = MonoidalClosed.internalHom) (hHD : HD = MonoidalClosed.internalHom)
    (hTC : TC = curriedTensor C) (hTD : TD = curriedTensor D)
    (b : ∀ K M, F.obj ((HC.obj (op K)).obj M) ⟶
      (HD.obj (op (F.obj K))).obj (F.obj M))
    (hb : HEq b (fun K M ↦
      (Functor.LaxMonoidal.ihomComparison F K).app M))
    (t : ∀ K M, (TD.obj (F.obj K)).obj (F.obj M) ⟶ F.obj ((TC.obj K).obj M))
    (ht : HEq t (fun K M ↦ Functor.LaxMonoidal.μ F K M))
    {W : C} {W' : D} (ω : F.obj W ≅ W')
    (P Q : ObjectProperty C) (P' : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [P'.IsClosedUnderIsomorphisms]
    (hD : ∀ K, P K → P ((HC.obj (op K)).obj W))
    (hHom : ∀ K M, P K → Q M → IsIso (b K M)) (hW : Q W)
    (EC : C → Prop) (ED : D → Prop)
    (hC : EC W) (hDpair : ED W')
    (evC : ∀ W, EC W → ∀ K, (TC.obj ((HC.obj (op K)).obj W)).obj K ⟶ W)
    (evD : ∀ W, ED W → ∀ K, (TD.obj ((HD.obj (op K)).obj W)).obj K ⟶ W)
    (ddC : ∀ W, EC W → ∀ K, K ⟶ (dualityDoubleFunctor HC W).obj K)
    (ddD : ∀ W, ED W → ∀ K, K ⟶ (dualityDoubleFunctor HD W).obj K)
    (hevC : HEq (evC W hC) (fun K ↦ (β_ ((ihom K).obj W) K).hom ≫ (ihom.ev K).app W))
    (hevD : HEq (evD W' hDpair) (fun K ↦ (β_ ((ihom K).obj W') K).hom ≫ (ihom.ev K).app W'))
    (hddC : HEq (ddC W hC) (fun K ↦ MonoidalClosed.toIhomIhom W K))
    (hddD : HEq (ddD W' hDpair) (fun K ↦ MonoidalClosed.toIhomIhom W' K))
    (hδ : ∀ K, P K → IsIso (MonoidalClosed.toIhomIhom W K))
    (e : P.FullSubcategory ≌ P'.FullSubcategory)
    (he : e.functor ⋙ P'.ι ≅ P.ι ⋙ F) :
    EvaluationDualityData F HC HD TC TD b t EC ED evC evD ddC ddD
      W W' ω.hom P Q P' := by
  let : F.LaxBraided := { braided := hbraiding }
  let : F.Braided := {}
  have h := comparisonData_raw F HC HD TC TD hHC hHD hTC hTD b hb t ht ω P P'
    hD (fun K hK ↦ hHom K W hK hW) (evC W hC) (evD W' hDpair)
    (ddC W hC) (ddD W' hDpair) hevC hevD hddC hddD
    (by subst HC; exact fun K hK ↦ (congrFun (eq_of_heq hddC) K).symm ▸ hδ K hK)
    e he
  exact ⟨hHom, ω, rfl, hC, hDpair, h.1, ⟨e, ⟨he⟩⟩, h.2⟩

private theorem bounded_iff_finite_support
    {C : Type c} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : DerivedCategory C) :
    DerivedCategory.TStructure.t.bounded K ↔
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)} := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    apply (Set.finite_Icc a b).subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi ((DerivedCategory.isGE_iff K a).mp ha i h)),
      le_of_not_gt (fun h ↦ hi ((DerivedCategory.isLE_iff K b).mp hb i h))⟩
  · intro h
    obtain ⟨a, ha⟩ := h.bddBelow
    obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨⟨a, (DerivedCategory.isGE_iff K a).mpr (fun i hi ↦ ?_)⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).mpr (fun i hi ↦ ?_)⟩⟩
    · by_contra hz
      exact (not_lt_of_ge (ha hz)) hi
    · by_contra hz
      exact (not_lt_of_ge (hb hz)) hi

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The canonical map from the etale constant unit to the derived direct image of the
pro-etale constant unit: the comparison adjunction unit followed by constant transport.
Source: blueprint order 2084, proof step 9
(blueprint: proposition-six-operations-dctf--15). -/
noncomputable def finiteDualityBaseUnit
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (S : Scheme.{u})
    (ε : (comparisonUpperStar A S).obj (𝟙_ _) ⟶ 𝟙_ _) :
    (𝟙_ (DerivedCategory (Sheaf S.smallEtaleTopology A))) ⟶
      (comparisonLowerStar A S).rightDerivedFunctor.obj (𝟙_ _) :=
  (derivedComparisonAdjunction A S).unit.app (𝟙_ _) ≫
    (comparisonLowerStar A S).rightDerivedFunctor.map
      (finiteDualitySingleTransport (comparisonUpperStar A S) ε
        (DerivedCategory.singleFunctorObjUnitIso _)
        (DerivedCategory.singleFunctorObjUnitIso _))

/-- The ordinary etale dualizing object using the specified compactification.
This instantiates the existing ambient compact-support right adjoint; no adjoint
hypothesis on the pro-etale category is introduced.
Source: blueprint order 2084, definition of omega_et
(blueprint: proposition-six-operations-dctf--15). -/
noncomputable def finiteDualityEtaleObject
    (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  letI := c.hasCompactification
  Etale.dualizingComplex (ULift.{u + 1, u} A) a

/-- The pro-etale dualizing object is the recorded comparison-transport exceptional
inverse image applied to the pro-etale constant unit.
Source: blueprint order 2084, definition of omega_proet
(blueprint: proposition-six-operations-dctf--15). -/
noncomputable def finiteDualityProEtaleObject
    (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  (sfFiniteExceptionalFixed A c).obj (𝟙_ _)

/-- The canonical dualizing-object arrow: apply the etale exceptional inverse image
and then comparison pullback to the comparison adjunction unit at the base constant unit.
This formula supplies the global overlap normalization of the dualizing comparison.
Source: blueprint order 2084, proof step 9
(blueprint: proposition-six-operations-dctf--15). -/
noncomputable def finiteDualityObjectMap
    (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a) :
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj
        (finiteDualityEtaleObject A c) ⟶ finiteDualityProEtaleObject A c :=
  letI := c.hasCompactification
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.map
    ((Etale.rightDerivedUpperShriek (ULift.{u + 1, u} A) a).map
      (finiteDualityBaseUnit (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) S
        (comparisonUpperStarUnitIso (ULift.{u + 1, u} A) S).hom))

/-- The native double-dual arrow with the specified etale Koszul symmetry. -/
noncomputable def finiteDualityNativeBidual
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (W : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    K ⟶ (dualityDoubleFunctor (Etale.derivedHom A X) W).obj K :=
  let : BraidedCategory (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
    _root_.DerivedCategory.braidedCategory' _
  MonoidalClosed.toIhomIhom W K

/-- Native evaluation with the canonical descended symmetry. -/
noncomputable def nativeEtaleEvaluation
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
    (W K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((Etale.derivedTensor A X).obj (((Etale.derivedHom A X).obj (op K)).obj W)).obj K ⟶ W :=
  let : BraidedCategory (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
    _root_.DerivedCategory.braidedCategory' _
  (β_ (((Etale.derivedHom A X).obj (op K)).obj W) K).hom ≫ (ihom.ev K).app W

/-- Native pro-etale evaluation with the canonical descended symmetry. -/
noncomputable def nativeProEtaleEvaluation
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
    (W K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((derivedTensor A X).obj (((derivedHom A X).obj (op K)).obj W)).obj K ⟶ W :=
  let := DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology X) A)
  (β_ (((derivedHom A X).obj (op K)).obj W) K).hom ≫ (ihom.ev K).app W

/-- Native pro-etale biduality with the canonical descended symmetry. -/
noncomputable def nativeProEtaleBiduality
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
    (W K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    K ⟶ (dualityDoubleFunctor (derivedHom A X) W).obj K :=
  let := DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology X) A)
  MonoidalClosed.toIhomIhom W K

set_option linter.unusedVariables false in
/-- The site-comparison and Verdier-duality assertions for the supplied, fixed ambient
objects and constructibility predicates. All comparison arrows and normalized pairings
are the recorded ones; the coefficient specialization fixes every parameter below.
Source: blueprint order 2084, final paragraph
(blueprint: proposition-six-operations-dctf--15). -/
noncomputable def FiniteDualityComparisonData
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (W : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (w : (comparisonUpperStar A X).mapDerivedCategory.obj W ⟶ W')
    (Pet Qet : ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (Ppro : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))) : Prop :=
  CategoryTheory.EvaluationDualityData (comparisonUpperStar A X).mapDerivedCategory
    (Etale.derivedHom A X) (derivedHom A X)
    (Etale.derivedTensor A X) (derivedTensor A X)
    (siteComparisonEvaluationHom A X)
    (fun K M ↦ (siteComparisonTensorIso A X K).inv.app M)
    (Etale.AmbientDualityPairing A X) (AmbientDualityPairing A X)
    (fun W _ ↦ nativeEtaleEvaluation A X W) (fun W _ ↦ nativeProEtaleEvaluation A X W)
    (fun W _ ↦ finiteDualityNativeBidual A X W)
    (fun W _ ↦ nativeProEtaleBiduality A X W) W W' w Pet Qet Ppro

private theorem siteComparisonMonoidal_oplax
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat] :
    (siteComparisonMonoidal A X).toOplaxMonoidal =
      (comparisonAdjunction A X).leftAdjointOplaxMonoidal := by
  unfold siteComparisonMonoidal
  rfl

@[instance_reducible]
private noncomputable def siteComparison_braided
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat] :
    let := siteComparisonDerivedMonoidal A X
    let := DerivedCategory.symmetricCategory (Sheaf X.smallEtaleTopology A)
    let := DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology X) A)
    (comparisonUpperStar A X).mapDerivedCategory.Braided := by
  let := DerivedCategory.symmetricCategory (Sheaf X.smallEtaleTopology A)
  let := DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology X) A)
  let : (comparisonLowerStar A X).LaxMonoidal := by
    unfold comparisonLowerStar
    infer_instance
  let : (comparisonLowerStar A X).LaxBraided := by
    unfold comparisonLowerStar
    infer_instance
  let F := comparisonUpperStar A X
  let m : F.Monoidal := siteComparisonMonoidal A X
  let : F.OplaxMonoidal := m.toOplaxMonoidal
  let : F.mapDerivedCategory.Monoidal := siteComparisonDerivedMonoidal A X
  have hF (K M : Sheaf X.smallEtaleTopology A) :
      F.map (β_ K M).hom ≫ Functor.OplaxMonoidal.δ F M K =
        Functor.OplaxMonoidal.δ F K M ≫ (β_ (F.obj K) (F.obj M)).hom := by
    change _ ≫ @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F m.toOplaxMonoidal M K =
      @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F m.toOplaxMonoidal K M ≫ _
    change _ ≫ @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F
      (siteComparisonMonoidal A X).toOplaxMonoidal M K =
      @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F
        (siteComparisonMonoidal A X).toOplaxMonoidal K M ≫ _
    rw [siteComparisonMonoidal_oplax A X]
    exact ((comparisonAdjunction A X).leftAdjointOplaxMonoidal_δ_braiding
      K M).symm
  let : F.leftDerivedFunctor.Monoidal := F.leftDerivedFunctorMonoidal
  refine { toMonoidal := siteComparisonDerivedMonoidal A X, braided := ?_ }
  apply Functor.Monoidal.μ_braiding_of_δ_braiding
  intro K M
  exact (CategoryTheory.transported_braiding F.leftDerivedFunctor F.mapDerivedCategory
    F.leftDerivedFunctorIsoMapDerivedCategory
    (siteComparisonDerivedMonoidal_δ A X)
    (F.leftDerivedFunctor_map_braiding_hom_δ hF) K M).symm

/-- The normalized pro-etale pairing has canonical evaluation and biduality maps.
Source: blueprint order 2084, normalization of the ambient pairing
(blueprint: proposition-six-operations-dctf--15). -/
theorem pairing_normalized
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (h : AmbientDualityPairing A X W)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    let := DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology X) A)
    h.choose_spec.2.choose K =
      (β_ ((ihom K).obj W) K).hom ≫
        (ihom.ev K).app W ∧
      AmbientDualityPairing.bidualityMap A X h K =
        MonoidalClosed.toIhomIhom W K := by
  let := DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology X) A)
  exact CategoryTheory.normalized_pairing_choice W _ _ h
    (fun b hb K L ↦ (hb K L).trans (CategoryTheory.native_braiding K L)) K

private theorem etale_biduality_native
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.verdierDualDoubleDual Λ a).app K =
      finiteDualityNativeBidual (ModuleCat.{u + 1} Λ) X (Etale.dualizingComplex Λ a) K := by
  exact CategoryTheory.native_toIhomIhom (Etale.dualizingComplex Λ a) K

private theorem isIso_siteHom_of_iso
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hb : ∃ b, K.IsLE b) (hc : ∃ c, M.IsGE c)
    (h : Nonempty ((comparisonUpperStar A X).mapDerivedCategory.obj
        (((Etale.derivedHom A X).obj (op K)).obj M) ≅
      ((derivedHom A X).obj (op ((comparisonUpperStar A X).mapDerivedCategory.obj K))).obj
        ((comparisonUpperStar A X).mapDerivedCategory.obj M))) :
    IsIso (siteComparisonEvaluationHom A X K M) := by
  let : (comparisonUpperStar A X).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal A X
  obtain ⟨b, hb⟩ := hb
  obtain ⟨c, hc⟩ := hc
  have : ((ihom K).obj M).IsGE (c - b) :=
    DerivedCategory.isGE_obj_of_adjunction (ihom.adjunction K) M b c
  have := isIso_derivedComparisonAdjunction_unit_app A X M ⟨c, hc⟩
  have := isIso_derivedComparisonAdjunction_unit_app A X
    ((ihom K).obj M) ⟨c - b, inferInstance⟩
  unfold siteComparisonEvaluationHom
  exact CategoryTheory.isIso_comparisonHom _ _ (derivedComparisonAdjunction A X) K M h

section HomGeneratorComparison
attribute [local irreducible] DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stratumAdjointsComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    ∃ a : LocallyClosedComparisonAdjoints A c,
      ∀ (M : Etale.DerivedCategoryModule A X)
        (_hM : DerivedCategory.TStructure.t.plus M),
        DerivedCategory.TStructure.t.plus ((a.etaleRight v).obj M) ∧
        Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj
          ((a.etaleRight v).obj M) ≅
          (a.proetaleRight v).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)) := by
  let W : V.Opens := ⟨(Set.range c)ᶜ,
    (IsClosedImmersion.isClosedEmbedding c).isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace V := v.isEmbedding.isInducing.noetherianSpace
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  have : CompactSpace V :=
    ⟨TopologicalSpace.NoetherianSpace.isCompact Set.univ⟩
  have : TopologicalSpace.NoetherianSpace W := W.ι.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := inferInstance
  have hij : IsCompl (Set.range c) (Set.range W.ι) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  let _ : (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) c).IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A c
  let a : LocallyClosedComparisonAdjoints A c := {
    etale := (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.rightAdjoint
    proetale := (closedUpperShriek (ModuleCat.{u + 1} A) c W.ι).rightDerivedFunctor
    etaleAdjunction := Adjunction.ofIsLeftAdjoint _
    proetaleAdjunction := derivedLowerStarClosedUpperShriekAdjunction c W.ι hij }
  refine ⟨a, ?_⟩
  intro M hM
  let N := (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj M
  have hN : DerivedCategory.TStructure.t.plus N := by
    obtain ⟨k, hk⟩ := hM
    let : M.IsGE k := hk
    exact ⟨k, Functor.isGE_mapDerivedCategory_obj _ M k⟩
  obtain ⟨L, ⟨e⟩⟩ := closedRightAdjoint_boundedBelow A c N hN
  let α := finiteDualityClosedComparisonAlpha c W.ι
    (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) c) a.etale
    (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor a.proetale
    (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory
    (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory
    a.etaleAdjunction a.proetaleAdjunction N
    (asIso (finiteDualityClosedComparisonDelta c _ L e))
  have : IsIso α := closedComparisonAlpha_isIso A c W.ι hij N hN L e
  let r := (Functor.mapDerivedCategoryCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)
      (upperStar (ModuleCat.{u + 1} A) v)) ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} A) v) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  exact ⟨DerivedCategory.TStructure.t.plus.prop_of_iso e.symm L.property,
    ⟨asIso α ≪≫ a.proetale.mapIso (r.symm.app M)⟩⟩

private theorem isIso_lisseHom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S : Scheme.{u}} (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    [Scheme.IsFiniteLocallyConstantSheaf L] (hf : ObjectProperty.flat L)
    (N : Etale.DerivedCategoryModule A S) :
    IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) S
      ((DerivedCategory.singleFunctor _ 0).obj L) N) := by
  obtain ⟨Q, _, ⟨hQ⟩⟩ := lisse_pairing A L hf
  let := hQ
  let : (comparisonUpperStar (ModuleCat.{u + 1} A) S).PreservesFlat :=
    preservesFlat_comparisonUpperStar (X := S)
  exact site_iso_of_pairing (ModuleCat.{u + 1} A) S Q _ N

private theorem isIso_stratumHom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] [QuasiCompact (c ≫ v)]
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    [Scheme.IsFiniteLocallyConstantSheaf L] (hf : ObjectProperty.flat L)
    (M : Etale.BoundedConstructibleDerivedCategory A X) :
    IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
      ((locallyClosedEtaleExtension A c v).obj
        ((DerivedCategory.singleFunctor _ 0).obj L)) M.obj) := by
  obtain ⟨a, ha⟩ := stratumAdjointsComparison A c v
  obtain ⟨χe, _⟩ := StratumHomComparisonMate.etaleNormalizedIso A c v a
  obtain ⟨χp, _⟩ := StratumHomComparisonMate.proetaleNormalizedIso A c v a
  have hM : DerivedCategory.TStructure.t.plus M.obj := by
    obtain ⟨k, b, _, hz⟩ := M.property.2
    exact ⟨k, (DerivedCategory.isGE_iff M.obj k).mpr (fun i hi ↦ hz i (.inl hi))⟩
  obtain ⟨hN, ⟨γ⟩⟩ := ha M.obj hM
  let P := (DerivedCategory.singleFunctor _ 0).obj L
  have hH := StratumHomComparisonMate.etaleHom_bounded A L
    ((a.etaleRight v).obj M.obj) hN
  have hβ := isIso_lisseHom A L hf ((a.etaleRight v).obj M.obj)
  have := hβ
  let H := ((Etale.derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
    ((a.etaleRight v).obj M.obj)
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let G := (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory
  let eH := asIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) S P
    ((a.etaleRight v).obj M.obj)) ≪≫
    ((derivedHom (ModuleCat.{u + 1} A) S).obj (op (G.obj P))).mapIso γ
  let eD := (fixedDirectImageComparisonIso A (c ≫ v)).app ⟨H, hH⟩
  let eQ := (locallyClosedExtensionComparison A c v).app
    ⟨P, ⟨0, inferInstance⟩⟩
  let e := F.mapIso (χe.app (op P, M.obj)) ≪≫ eD ≪≫
    ((lowerStar (ModuleCat.{u + 1} A) (c ≫ v)).rightDerivedFunctor).mapIso eH ≪≫
    (χp.app (op (G.obj P), F.obj M.obj)).symm ≪≫
    (((derivedHom (ModuleCat.{u + 1} A) X).mapIso eQ.op).app (F.obj M.obj))
  let : (comparisonUpperStar (ModuleCat.{u + 1} A) X).PreservesFlat :=
    preservesFlat_comparisonUpperStar (X := X)
  apply isIso_siteHom_of_iso (ModuleCat.{u + 1} A) X _ M.obj ?_ hM ⟨e⟩
  · have : ((Etale.lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategory.obj P).IsLE 0 :=
      Functor.isLE_mapDerivedCategory_obj _ P 0
    have : ((Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.obj P).IsLE 0 :=
      DerivedCategory.TStructure.t.isLE_of_iso
        ((Etale.lowerStar (ModuleCat.{u + 1} A) c
          ).rightDerivedFunctorIsoMapDerivedCategory.app P).symm 0
    exact ⟨0, Functor.isLE_mapDerivedCategory_obj _ _ 0⟩

private theorem isIso_siteHom
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] {p : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasInvertibleExponent Λ X]
    (K M : Etale.DerivedCategoryModule Λ X)
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X K M) := by
  let : IsNoetherian X := {
    __ := LocallyOfFiniteType.isLocallyNoetherian aX
    __ := QuasiCompact.compactSpace_of_compactSpace aX }
  let : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).PreservesFlat :=
    preservesFlat_comparisonUpperStar (X := X)
  let P := siteHomComparisonLocus Λ X M
  have ht := siteHomComparison_exact_thick Λ X M
  unfold siteHomSiteExactThick siteHomExactThickAssertion at ht
  obtain ⟨sB, sE, β, hβ, _, htri, hret⟩ := ht
  have : P.IsTriangulated := htri
  have : P.IsStableUnderRetracts := hret
  have : P.IsClosedUnderIsomorphisms := by
    refine ⟨fun {B C} e hB ↦ ?_⟩
    change IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X B M) at hB
    have : IsIso (β.app (op B)) := by simpa only [hβ] using hB
    have : IsIso (β.app (op C)) := NatTrans.isIso_app_of_iso β e.op
    change IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X C M)
    simpa only [hβ] using (inferInstance : IsIso (β.app (op C)))
  apply boundedConstructible_induction X Λ P ?_ K
    ((WeilConjectures.boundedConstructible_iff_source Λ X K).mpr hK.1) ?_
  · rintro B ⟨str, i, j, hj, L, hji, hL, hf, ⟨e⟩⟩
    let := hj
    let := hL
    have hs : IsImmersion (str.immersion i) := str.isImmersion i
    let := hs
    have : TopologicalSpace.NoetherianSpace (str.domain i) :=
      (str.immersion i).isEmbedding.isInducing.noetherianSpace
    let c := (str.immersion i).liftCoborder
    let v := (str.immersion i).coborderRange.ι
    have hcv : c ≫ v = str.immersion i := (str.immersion i).liftCoborder_ι
    have : QuasiCompact (c ≫ v) := by rw [hcv]; infer_instance
    have hb := isIso_stratumHom Λ c v L hf
      ⟨M, (WeilConjectures.boundedConstructible_iff_source Λ X M).mpr hM⟩
    have hj' : j = (str.immersion i).toImage := by
      apply (cancel_mono (str.immersion i).imageι).mp
      exact hji.trans (Scheme.Hom.toImage_imageι _).symm
    subst j
    obtain ⟨_, he, _⟩ :=
      (etale_locallyClosed_extension_comparison (A := Λ) X (𝟙 X) v).2
        (str.immersion i)
    obtain ⟨es, _, _⟩ := he c v hcv
    have e' : (DerivedCategory.singleFunctor _ 0).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (str.immersion i).imageι).obj
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
            (str.immersion i).toImage).obj L)) ≅
        (locallyClosedEtaleExtension Λ c v).obj
          ((DerivedCategory.singleFunctor _ 0).obj L) := by
      let Q := Etale.lowerStar (ModuleCat.{u + 1} Λ) c ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) v
      have ee : (Etale.lowerStar (ModuleCat.{u + 1} Λ) (str.immersion i).imageι).obj
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
            (str.immersion i).toImage).obj L) ≅ Q.obj L := by
        exact es.app L
      exact (DerivedCategory.singleFunctor _ 0).mapIso ee ≪≫
        ((Q.mapDerivedCategorySingleFunctor 0).app L).symm ≪≫
        (Functor.mapDerivedCategoryCompIso
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) c)
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) v)).symm.app _ ≪≫
        (StratumHomComparisonMate.Etale.extensionIso Λ c v).symm.app _
    exact P.prop_of_iso (e ≪≫ e').symm hb
  · obtain ⟨a, b, ht⟩ := hK.2
    refine ⟨min a b, b, min_le_right _ _, ?_⟩
    exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      (Etale.DerivedCategory.torAmplitudeIn.mono (min_le_left _ _) le_rfl ht)

end HomGeneratorComparison

attribute [local irreducible] DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution in
private theorem comparisonData_of
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (W : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (ω : (comparisonUpperStar A X).mapDerivedCategory.obj W ≅ W')
    (P Q : ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (P' : ObjectProperty (DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) A)))
    [P.IsClosedUnderIsomorphisms] [P'.IsClosedUnderIsomorphisms]
    (hHom : ∀ K M, P K → Q M →
      IsIso (siteComparisonEvaluationHom A X K M))
    (hW : Q W)
    (hD : ∀ K, P K → P (((Etale.derivedHom A X).obj (op K)).obj W))
    (hEt : Etale.AmbientDualityPairing A X W)
    (hPro : AmbientDualityPairing A X W')
    (hδ : ∀ K, P K → IsIso (finiteDualityNativeBidual A X W K))
    (e : P.FullSubcategory ≌ P'.FullSubcategory)
    (he : e.functor ⋙ P'.ι ≅ P.ι ⋙
      (comparisonUpperStar A X).mapDerivedCategory) :
    FiniteDualityComparisonData A X W W' ω.hom P Q P' := by
  classical
  let := DerivedCategory.symmetricCategory (Sheaf X.smallEtaleTopology A)
  let := DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology X) A)
  let F := (comparisonUpperStar A X).mapDerivedCategory
  let : F.Monoidal := siteComparisonDerivedMonoidal A X
  exact CategoryTheory.comparisonData_allPairings (W := W) (W' := W') F
    (fun K M ↦ (siteComparison_braided A X).braided K M)
    (Etale.derivedHom A X) (derivedHom A X)
    (Etale.derivedTensor A X) (derivedTensor A X) rfl rfl rfl rfl
    (siteComparisonEvaluationHom A X) (by unfold siteComparisonEvaluationHom; rfl)
    (fun K M ↦ (siteComparisonTensorIso A X K).inv.app M)
    (by unfold siteComparisonTensorIso; rfl)
    ω P Q P' hD hHom hW
    (Etale.AmbientDualityPairing A X) (AmbientDualityPairing A X)
    hEt hPro
    (fun W _ ↦ nativeEtaleEvaluation A X W) (fun W _ ↦ nativeProEtaleEvaluation A X W)
    (fun W _ ↦ finiteDualityNativeBidual A X W) (fun W _ ↦ nativeProEtaleBiduality A X W)
    (HEq.refl _) (HEq.refl _) (HEq.refl _) (HEq.refl _)
    (fun K hK ↦ hδ K hK) e he

private theorem comparisonData_of_verdier
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]
    [(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).PreservesFlat]
    (W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (w : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
      (Etale.dualizingComplex Λ a) ⟶ W')
    (hw : IsIso w)
    (P Q : ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (P' : ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))))
    [P.IsClosedUnderIsomorphisms] [P'.IsClosedUnderIsomorphisms]
    (hHom : ∀ K M, P K → Q M →
      IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X K M))
    (hW : Q (Etale.dualizingComplex Λ a))
    (hD : ∀ K, P K → P ((Etale.verdierDual Λ a).obj (op K)))
    (hδ : ∀ K, P K → IsIso ((Etale.verdierDualDoubleDual Λ a).app K))
    (hEt : Etale.AmbientDualityPairing (ModuleCat.{u + 1} Λ) X (Etale.dualizingComplex Λ a))
    (hPro : AmbientDualityPairing (ModuleCat.{u + 1} Λ) X W')
    (e : P.FullSubcategory ≌ P'.FullSubcategory)
    (he : e.functor ⋙ P'.ι ≅
      P.ι ⋙ (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory) :
    FiniteDualityComparisonData (ModuleCat.{u + 1} Λ) X (Etale.dualizingComplex Λ a) W' w
      P Q P' := by
  apply comparisonData_of (ModuleCat.{u + 1} Λ) X _ _ (@asIso _ _ _ _ w hw) P Q P' hHom hW hD
    hEt hPro ?_ e he
  intro K hK
  rw [← etale_biduality_native Λ a K]
  exact hδ K hK

private theorem isIso_singleTransport
    {C : Type c} [Category.{v} C] [Abelian C] [HasDerivedCategory.{v} C]
    {D : Type d} [Category.{w} D] [Abelian D] [HasDerivedCategory.{w} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {V : C} {V' : D} (ε : F.obj V ⟶ V') [IsIso ε]
    {U : DerivedCategory C} {U' : DerivedCategory D}
    (i : (DerivedCategory.singleFunctor C 0).obj V ≅ U)
    (j : (DerivedCategory.singleFunctor D 0).obj V' ≅ U') :
    IsIso (finiteDualitySingleTransport F ε i j) := by
  unfold finiteDualitySingleTransport
  infer_instance

private theorem isIso_baseUnit
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (S : Scheme.{u})
    (ε : (comparisonUpperStar A S).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso ε] :
    IsIso (finiteDualityBaseUnit A S ε) := by
  have hs := isIso_singleTransport (comparisonUpperStar A S) ε
    (DerivedCategory.singleFunctorObjUnitIso _)
    (DerivedCategory.singleFunctorObjUnitIso _)
  have hu := isIso_derivedComparisonAdjunction_unit_app A S
    (𝟙_ _) (by
      refine ⟨0, ?_⟩
      exact DerivedCategory.TStructure.t.isGE_of_iso
        (DerivedCategory.singleFunctorObjUnitIso _) 0)
  unfold finiteDualityBaseUnit
  infer_instance

private theorem isIso_objectMap
    (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a) :
    IsIso (finiteDualityObjectMap A c) := by
  let := c.hasCompactification
  let b := finiteDualityBaseUnit (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) S
    (comparisonUpperStarUnitIso (ULift.{u + 1, u} A) S).hom
  have : IsIso b := isIso_baseUnit (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) S
    (comparisonUpperStarUnitIso (ULift.{u + 1, u} A) S).hom
  let e := ((comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory).mapIso
    ((Etale.rightDerivedUpperShriek
      (ULift.{u + 1, u} A) a).mapIso (asIso b))
  change IsIso e.hom
  infer_instance

private theorem dualizing_boundedConstructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    Etale.DerivedCategory.boundedConstructible (ModuleCat Λ) X
      (Etale.dualizingComplex Λ a) := by
  exact Etale.boundedConstructible_rightDerivedUpperShriek Λ (𝟙 _) a
    ((Etale.DerivedCategory.boundedConstructible _ _).prop_of_iso
      (DerivedCategory.singleFunctorObjUnitIso _)
      (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0))

private theorem finiteRingComparisonData
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] {p : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    [HasInvertibleExponent (Λ) (Spec (.of k))]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [HasCompactification a]
    (W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (w : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
      (Etale.dualizingComplex Λ a) ⟶ W')
    (hw : IsIso w)
    (P Q : ObjectProperty (Etale.DerivedCategoryModule (Λ) X))
    (P' : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (Λ)))))
    (hP : ∀ K, P K ↔ Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Λ)) X K)
    (hQ : ∀ K, Q K ↔ Etale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (Λ)) X K)
    [P.IsClosedUnderIsomorphisms] [P'.IsClosedUnderIsomorphisms]
    (e : P.FullSubcategory ≌ P'.FullSubcategory)
    (he : e.functor ⋙ P'.ι ≅ P.ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} (Λ)) X).mapDerivedCategory) :
    FiniteDualityComparisonData (ModuleCat.{u + 1} (Λ)) X
      (Etale.dualizingComplex Λ a) W'
      w P Q P' := by
  have : IsAlgClosed k := IsAlgClosure.isAlgClosed (ZMod p)
  have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom a
  have : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).PreservesFlat :=
    preservesFlat_comparisonUpperStar (X := X)
  have hHom : ∀ K M, P K → Q M →
      IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X K M) := by
    intro K M hK hM
    exact isIso_siteHom Λ (p := p) a K M ((hP K).mp hK) ((hQ M).mp hM)
  have hW : Q (Etale.dualizingComplex Λ a) :=
    (hQ _).mpr (dualizing_boundedConstructible Λ a)
  have hEt := (Etale.ambient_duality_pairing Λ a).1
  have hPro := (Etale.ambient_duality_pairing Λ a).2 W'
  exact comparisonData_of_verdier Λ a _
    w hw P Q P' hHom hW
    (fun K hK ↦ (hP _).mpr (Etale.constructibleFiniteTor_verdierDual Λ a ((hP K).mp hK)))
    (fun K hK ↦ Etale.isIso_verdierDualDoubleDual_app Λ a ((hP K).mp hK))
    hEt hPro e he

private theorem finiteComparisonData_core
    (A : Type u) [CommRing A] [Finite A]
    {k : Type u} [Field k] {p : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    [HasInvertibleExponent (ULift.{u + 1, u} A) (Spec (.of k))]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (P Q : ObjectProperty (Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X))
    (P' : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))))
    (hP : ∀ K, P K ↔ Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X K)
    (hQ : ∀ K, Q K ↔ Etale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X K)
    [P.IsClosedUnderIsomorphisms] [P'.IsClosedUnderIsomorphisms]
    (e : P.FullSubcategory ≌ P'.FullSubcategory)
    (he : e.functor ⋙ P'.ι ≅ P.ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory) :
    let c := NagataCompactification a
    let := c.hasCompactification
    FiniteDualityComparisonData (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
      (finiteDualityEtaleObject A c) (finiteDualityProEtaleObject A c)
      (finiteDualityObjectMap A c) P Q P' := by
  let Λ := ULift.{u + 1, u} A
  let c := NagataCompactification a
  exact finiteRingComparisonData Λ (p := p) a (finiteDualityProEtaleObject A c)
    (finiteDualityObjectMap A c) (isIso_objectMap A c) P Q P' hP hQ e he

end AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- The finite-stage comparison conclusion. Each abbreviation inside this definition
is the existing canonical object or functor. In particular the two dualizing objects
are fixed before the comparison isomorphism is quantified. Its hom is prescribed by
the base adjunction unit, and the Hom comparison is prescribed by evaluation.
The last clauses record the induced equivalence of finite-Tor constructible categories,
the anti-equivalence with the specified Verdier functor, and its canonical biduality map.
Source: blueprint order 2084 (blueprint: proposition-six-operations-dctf--15). -/
noncomputable def FiniteDualitySiteComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let A := Padic.coefficientExtensionRing l E n
  let Λ := ULift.{u + 1, u} A
  letI : Finite Λ := inferInstance
  letI : IsNoetherianRing Λ := isNoetherian_of_finite Λ Λ
  letI : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar (X := X)
  let c := NagataCompactification (X ↘ Spec (.of D.k))
  ProEtale.FiniteDualityComparisonData (ModuleCat.{u + 1} Λ) X
    (ProEtale.finiteDualityEtaleObject A c) (ProEtale.finiteDualityProEtaleObject A c)
    (ProEtale.finiteDualityObjectMap A c)
    (finiteTorConstructibleEtale l E n hn X)
    (Etale.DerivedCategory.isBoundedConstructible Λ X)
    (finiteTorConstructibleProEtaleModule l E n hn X)

private theorem finiteTor_proEtale_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))))) :
    finiteTorConstructibleProEtaleModule l E n hn X K ↔
      ProEtale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X K := by
  let A := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let Λ := ULift.{u + 1, u} A
  let F := ProEtale.finiteCoefficientIntrinsicRealization X A
  have : F.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact X A).1
  have hc (i : ℤ) :
      Scheme.IsConstructibleProEtaleModuleSheaf X A
        ((DerivedCategory.homologyFunctor _ i).obj (F.mapDerivedCategory.obj K)) ↔
      ProEtale.IsConstructible Λ ((DerivedCategory.homologyFunctor _ i).obj K) := by
    let e := (F.mapDerivedCategoryHomologyFunctorIso i).app K
    constructor
    · intro h
      exact (Scheme.intrinsicRealization_constructible_iff X A _).mp
        (Scheme.intrinsicConstructible_of_iso X A e.symm h)
    · intro h
      exact Scheme.intrinsicConstructible_of_iso X A e
        ((Scheme.intrinsicRealization_constructible_iff X A _).mpr h)
  constructor
  · rintro ⟨⟨hb, hconstructible⟩, a, b, ht⟩
    have hbk : DerivedCategory.TStructure.t.bounded K :=
      F.bounded_of_bounded_mapDerivedCategory_obj
        ((CategoryTheory.bounded_iff_finite_support _).mpr hb)
    have hbc := ProEtale.DerivedCategory.boundedConstructible_of_homology Λ hbk
      (fun i ↦ ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _
        ((hc i).mp (hconstructible i)))
    exact ⟨hbc, a, b,
      (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A X a b ht.1 K).mp ht⟩
  · intro h
    have hbci := ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic
      _ h.1
    refine ⟨⟨(CategoryTheory.bounded_iff_finite_support _).mp
      (F.bounded_mapDerivedCategory_obj hbci.1), fun i ↦ (hc i).mpr (hbci.2 i)⟩, ?_⟩
    obtain ⟨a, b, ht⟩ := h.2
    refine ⟨min a b, max a b, ?_⟩
    exact (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      A X (min a b) (max a b) min_le_max K).mpr
      (DerivedCategory.torAmplitudeIn.mono (min_le_left _ _) (le_max_right _ _) ht)

private theorem finiteTor_comparison_equivalence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) :
    ∃ e : (finiteTorConstructibleEtale l E n hn X).FullSubcategory ≌
        (finiteTorConstructibleProEtaleModule l E n hn X).FullSubcategory,
      Nonempty (e.functor ⋙ (finiteTorConstructibleProEtaleModule l E n hn X).ι ≅
        (finiteTorConstructibleEtale l E n hn X).ι ⋙
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).mapDerivedCategory) := by
  classical
  let A := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let Λ := ULift.{u + 1, u} A
  let F := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory
  let P := finiteTorConstructibleEtale l E n hn X
  let Q := finiteTorConstructibleProEtaleModule l E n hn X
  have hF (K : P.FullSubcategory) : Q (F.obj K.obj) :=
    (finiteTor_proEtale_iff l E n hn X _).mpr
      (ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory Λ
        ((finiteTorConstructibleEtale_iff_source l E n hn X _).mp K.property))
  let J := Q.lift (P.ι ⋙ F) hF
  have hplus (M : P.FullSubcategory) : DerivedCategory.TStructure.t.plus M.obj :=
    ((finiteTorConstructibleEtale_iff_source l E n hn X _).mp M.property).1.1.1
  have hb (K M : P.FullSubcategory) : Function.Bijective
      (fun f : K.obj ⟶ M.obj ↦ F.map f) :=
    ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map K.obj M.obj (hplus M)
  have : J.Full := ⟨fun {K M} f ↦ by
    obtain ⟨g, hg⟩ := (hb K M).2 f.hom
    exact ⟨P.homMk g, Q.hom_ext hg⟩⟩
  have : J.Faithful := ⟨fun {K M} f g h ↦
    P.hom_ext ((hb K M).1 (congrArg (·.hom) h))⟩
  have : J.EssSurj := ⟨fun K ↦ by
    have hK := (finiteTor_proEtale_iff l E n hn X K.obj).mp K.property
    obtain ⟨M, hM, ⟨e⟩⟩ := hK.1
    obtain ⟨a, b, ht⟩ := hK.2
    have ht' := (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm ht
    have hM' : P M := (finiteTorConstructibleEtale_iff_source l E n hn X M).mpr
      ⟨hM, a, b,
        (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b M).mp ht'⟩
    exact ⟨⟨M, hM'⟩, ⟨Q.isoMk e⟩⟩⟩
  have : J.IsEquivalence := {}
  exact ⟨J.asEquivalence, ⟨Iso.refl _⟩⟩

/-- The canonical evaluation comparison is invertible for a finite-Tor constructible
first input and a bounded constructible second input. The canonical dualizing comparison
identifies evaluations and their double-dual transposes, and transports Verdier duality.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation, order 2084
(blueprint: proposition-six-operations-dctf--15).

Proof:
1. Lisse finite flat sheaves have derived exact pairings, so their Hom comparison
   is invertible for every target. Closed-support comparison and exact open
   restriction identify stratum exceptional values on bounded-below inputs.
   The proved projection-adjunction Hom isomorphisms and ordinary direct-image
   comparison assemble an isomorphism of Hom objects on each stratum generator.
   For a strong monoidal left adjoint F, the adjunction calculation identifies
   R(beta) after the unit with Hom of the unit followed by a projection
   isomorphism. The units are invertible on M and RHom(K,M). The constructed
   object isomorphism makes the target counit invertible, so counit naturality
   proves that the canonical beta is invertible. Thick generation and the
   triangulated, retract-stable comparison locus extend this to every finite-Tor
   constructible source.
2. The specified dualizing comparison is obtained by applying the exceptional
   functor to the unit comparison. The comparison adjunction unit is invertible
   on the bounded-below constant unit, and the exact degree-zero transport is an
   isomorphism. Hence the prescribed dualizing arrow is an isomorphism.
3. Exact coefficient realization identifies intrinsic constructibility and Tor
   amplitude with their fixed-module predicates. Full faithfulness on bounded
   below complexes and constructible origin yield the comparison equivalence on
   finite-Tor constructible full subcategories.
4. Derive ordinary comparison pullback's braided tensor structure and transport
   it along the canonical derived-functor isomorphism. The prescribed tensor
   components determine the resulting braiding equation. Pairing normalization
   identifies the recorded evaluations and bidual maps with the native closed
   category evaluations and double-dual maps.
5. Apply evaluationBidualComparisonTransport to the canonical Hom comparisons,
   dualizing isomorphism, and full-subcategory equivalence. Etale geometric
   biduality supplies preservation by duality and invertibility of the source
   bidual map. The transport theorem gives both requested commuting equations,
   the target anti-equivalence, and invertibility of every target bidual map.
-/
theorem finite_duality_site_comparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    FiniteDualitySiteComparison D l hl E n hn X := by
  classical
  let A := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let Λ := ULift.{u + 1, u} A
  let a := X ↘ Spec (.of D.k)
  let c := NagataCompactification a
  let : IsNoetherianRing Λ := isNoetherian_of_finite Λ Λ
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Algebra (ZMod D.p) D.k₀ := ZMod.algebra D.k₀ D.p
  let : Algebra (ZMod D.p) D.k :=
    ((algebraMap D.k₀ D.k).comp (algebraMap (ZMod D.p) D.k₀)).toAlgebra
  let : IsScalarTower (ZMod D.p) D.k₀ D.k := IsScalarTower.of_algebraMap_eq' rfl
  let : IsAlgClosure (ZMod D.p) D.k := IsAlgClosure.ofAlgebraic (ZMod D.p) D.k₀ D.k
  have : HasInvertibleExponent Λ (Spec (.of D.k)) :=
    coefficient_invertible_exponent D l hl E n
  have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom a
  have : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar (X := X)
  let P := finiteTorConstructibleEtale l E n hn X
  let Q := Etale.DerivedCategory.isBoundedConstructible Λ X
  let P' := finiteTorConstructibleProEtaleModule l E n hn X
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    (finiteTorConstructibleEtale_iff_source l E n hn X _).mpr
      ((Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).prop_of_iso e
        ((finiteTorConstructibleEtale_iff_source l E n hn X _).mp h))⟩
  have : P'.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    (finiteTor_proEtale_iff l E n hn X _).mpr
      ((ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).prop_of_iso e
        ((finiteTor_proEtale_iff l E n hn X _).mp h))⟩
  obtain ⟨e, ⟨he⟩⟩ := finiteTor_comparison_equivalence l E n hn X
  exact ProEtale.finiteComparisonData_core A (p := D.p) a P Q P'
    (finiteTorConstructibleEtale_iff_source l E n hn X)
    (boundedConstructible_iff_source Λ X) e he

end WeilConjectures
