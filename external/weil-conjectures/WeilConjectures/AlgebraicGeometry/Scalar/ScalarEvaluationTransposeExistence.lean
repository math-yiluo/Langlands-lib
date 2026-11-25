/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import WeilConjectures.Algebra.Homology.System.SystemEvaluationKFlat
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Evaluation and transpose for normalized scalar data

## References

* Zheng, Construction 4.1 and Lemma 4.10
* Stacks 07A4 and 07A6
* Stacks 0FND and 09T5
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe c v r

open CategoryTheory CategoryTheory.Limits

private theorem exactSquare_fac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {R : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {S : C ⥤ D}
    [R.Additive] [G.Additive] [H.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (δ : R ⋙ G ≅ H ⋙ S) (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso δ).hom.app (DerivedCategory.Q.obj K) ≫
        S.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
        S.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
      G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((δ.hom.mapHomologicalComplex (.up ℤ)).app K) := by
  have hc := Functor.mapDerivedCategoryCompIso_hom_app_factors R G K
  have hi : (Functor.mapDerivedCategoryCompIso R G).hom.app (DerivedCategory.Q.obj K) ≫
      (R ⋙ G).mapDerivedCategoryFactors.hom.app K =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (cancel_epi
      ((Functor.mapDerivedCategoryCompIso R G).inv.app (DerivedCategory.Q.obj K))).mp
    rw [Iso.inv_hom_id_app_assoc]
    exact hc.symm
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc, hi, Category.assoc]

private theorem sequenceScalarMate_isIso
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C)
    (R S : Sheaf (WeilConjectures.coefficientSequenceTopology J) RingCat.{max c v r})
    (n : ℕ) (φ : R ⟶ S) (Rn Sn : Sheaf J RingCat.{max c v r})
    (hR : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{max c v r} J
      (WeilConjectures.coefficientSequenceTopology J)).obj R = Rn)
    (hS : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{max c v r} J
      (WeilConjectures.coefficientSequenceTopology J)).obj S = Sn)
    (ψ : Rn ⟶ Sn)
    (E : SheafOfModules.{max c v r} R ⥤ SheafOfModules.{max c v r} S)
    (En : SheafOfModules.{max c v r} Rn ⥤ SheafOfModules.{max c v r} Sn)
    (adj : E ⊣ SheafOfModules.restrictScalars φ)
    (adjn : En ⊣ SheafOfModules.restrictScalars ψ)
    (δ : SheafOfModules.restrictScalars φ ⋙
      SheafOfModules.pushforward (F := Prod.sectR n C) (eqToHom hR.symm) ≅
      SheafOfModules.pushforward (F := Prod.sectR n C) (eqToHom hS.symm) ⋙
        SheafOfModules.restrictScalars ψ) :
    IsIso ((mateEquiv adj adjn).symm (TwoSquare.mk _ _ _ _ δ.hom)) := by
  let : ((𝟭 ℕ).prod (𝟭 C)).IsContinuous
      (WeilConjectures.coefficientSequenceTopology J)
      (WeilConjectures.coefficientSequenceTopology J) := by
    change (𝟭 (ℕ × C)).IsContinuous _ _
    infer_instance
  exact WeilConjectures.SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
    J J (𝟭 C) R S n φ Rn Sn hR hS ψ E En adj adjn δ

section
universe a av b bv cv d dv a' av' b' bv' c' cv' d' dv'
open CategoryTheory CategoryTheory.Functor
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
  {AD : Type a'} [Category.{av'} AD] {BD : Type b'} [Category.{bv'} BD]
  {CD : Type c'} [Category.{cv'} CD] {DD : Type d'} [Category.{dv'} DD]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {LD₁ : AD ⥤ BD} {RD₁ : BD ⥤ AD} {LD₂ : CD ⥤ DD} {RD₂ : DD ⥤ CD}
  {G : A ⥤ C} {H : B ⥤ D} {GD : AD ⥤ CD} {HD : BD ⥤ DD}
  {QA : A ⥤ AD} {QB : B ⥤ BD} {QC : C ⥤ CD} {QD : D ⥤ DD}

/-- A derived mate is computed by the ordinary mate and the normalized derived
comparisons. -/
private theorem mate_comparison_at
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (ad₁ : LD₁ ⊣ RD₁) (ad₂ : LD₂ ⊣ RD₂)
    (ε₁ : QA ⋙ LD₁ ⟶ L₁ ⋙ QB) (ε₂ : QC ⋙ LD₂ ⟶ L₂ ⋙ QD)
    (ρ₁ : QB ⋙ RD₁ ≅ R₁ ⋙ QA) (ρ₂ : QD ⋙ RD₂ ≅ R₂ ⋙ QC)
    (γ : QA ⋙ GD ≅ G ⋙ QC) (η : QB ⋙ HD ≅ H ⋙ QD)
    (P : A)
    (h₁ : ∀ K (f : L₁.obj P ⟶ K),
      ad₁.homEquiv _ _ (ε₁.app P ≫ QB.map f) =
        QA.map (a₁.homEquiv _ _ f) ≫ ρ₁.inv.app K)
    (h₂ : ∀ K (f : L₂.obj (G.obj P) ⟶ K),
      ad₂.homEquiv _ _ (ε₂.app (G.obj P) ≫ QD.map f) =
        QC.map (a₂.homEquiv _ _ f) ≫ ρ₂.inv.app K)
    (τ : TwoSquare R₁ H G R₂) (τD : TwoSquare RD₁ HD GD RD₂)
    (hτ : ∀ K,
      τD.app (QB.obj K) ≫ RD₂.map (η.hom.app K) ≫ ρ₂.hom.app (H.obj K) =
        GD.map (ρ₁.hom.app K) ≫ γ.hom.app (R₁.obj K) ≫ QC.map (τ.app K))
    (ι : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (hι : ∀ P, a₂.homEquiv _ _ (ι.app P) = G.map (a₁.unit.app P) ≫ τ.app (L₁.obj P))
    :
    ((mateEquiv ad₁ ad₂).symm τD).app (QA.obj P) ≫
        HD.map (ε₁.app P) ≫ η.hom.app (L₁.obj P) =
      LD₂.map (γ.hom.app P) ≫ ε₂.app (G.obj P) ≫ QD.map (ι.app P) := by
  apply (ad₂.homEquiv _ _).injective
  apply (cancel_mono (ρ₂.hom.app (H.obj (L₁.obj P)))).1
  rw [← Category.assoc, ad₂.homEquiv_naturality_right, adjunctionMate_transpose]
  have he : ad₁.homEquiv _ _ (ε₁.app P) =
      QA.map (a₁.unit.app P) ≫ ρ₁.inv.app (L₁.obj P) := by
    have h := h₁ (L₁.obj P) (𝟙 _)
    erw [QB.map_id, Category.comp_id, a₁.homEquiv_unit,
      R₁.map_id, Category.comp_id] at h
    exact h
  rw [he, GD.map_comp]
  simp only [Category.assoc]
  erw [hτ]
  rw [← Category.assoc (GD.map (ρ₁.inv.app (L₁.obj P)))
    (GD.map (ρ₁.hom.app (L₁.obj P))), ← GD.map_comp, ρ₁.inv_hom_id_app,
    GD.map_id, Category.id_comp]
  change GD.map (QA.map (a₁.unit.app P)) ≫
    γ.hom.app (R₁.obj (L₁.obj P)) ≫ QC.map (τ.app (L₁.obj P)) = _
  rw [← Functor.comp_map]
  erw [γ.hom.naturality_assoc]
  rw [ad₂.homEquiv_naturality_left]
  erw [h₂]
  simp only [Category.assoc, ρ₂.inv_hom_id_app]
  erw [hι, QC.map_comp, Category.comp_id]
  rfl

end

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem evaluation_preservesKFlat (n : ℕ)
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := systemRing.{c, v, max c v r} J B τ) P)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := coefficientSequenceTopology J)
      (R := systemRing.{c, v, max c v r} J B τ) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := B n)
      (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P) := by
  have he : evaluation.{c, v, max c v r} J B τ n =
      SheafOfModules.systemSequenceEvaluation (rings.{c, v, max c v r} J B τ) n := by
    unfold evaluation SheafOfModules.systemSequenceEvaluation
    congr 1
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  simpa only [he] using (SheafOfModules.systemSequenceEvaluation_preservesKFlat
    (rings.{c, v, max c v r} J B τ) n P hP hf).1

/-- The evaluation comparison and its normalized adjunction transpose. -/
structure ScalarEvaluationData
    (F : ℕ → Sheaf J CommRingCat.{max c v r})
    (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
    (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n)
    (S : ScalarData.{c, v, max c v r}
      (systemMap.{c, v, max c v r} J B τ F σ α hα))
    (L : ∀ n : ℕ, ScalarData.{c, v, max c v r} (α n)) where
  evaluation : ∀ n : ℕ,
    S.T ⋙ e.{c, v, max c v r} J F σ n ≅
      e.{c, v, max c v r} J B τ n ⋙ (L n).T
  transpose_evaluation : ∀ (n : ℕ) (M : DS.{c, v, max c v r} J B τ)
    (N : DS.{c, v, max c v r} J F σ) (f : S.T.obj M ⟶ N),
    (e.{c, v, max c v r} J B τ n).map ((S.adjunction.homEquiv _ _) f) ≫
        (restrictionEvaluation.{c, v, max c v r} J B τ F σ α hα n).hom.app N =
      ((L n).adjunction.homEquiv _ _)
        ((evaluation n).inv.app M ≫ (e.{c, v, max c v r} J F σ n).map f)

-- Matching the normalized mate equations compares several large derived-functor types.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Existence of the level evaluation comparison normalized by the restriction mate. -/
theorem semilinearScalarEvaluationTranspose
    (F : ℕ → Sheaf J CommRingCat.{max c v r})
    (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
    (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n)
    (S : ScalarData.{c, v, max c v r}
      (systemMap.{c, v, max c v r} J B τ F σ α hα))
    (L : ∀ n : ℕ, ScalarData.{c, v, max c v r} (α n)) :
    Nonempty (ScalarEvaluationData.{c, v, r} J B τ F σ α hα S L) := by
  classical
  let G := evaluation.{c, v, max c v r} J B τ
  let H := evaluation.{c, v, max c v r} J F σ
  let R := res.{c, v, max c v r}
    (systemMap.{c, v, max c v r} J B τ F σ α hα)
  let Rn := fun n ↦ res.{c, v, max c v r} (α n)
  let δ := fun n ↦
    (restrictionEvaluation_existsUnique.{c, v, max c v r} J B τ F σ α hα n).exists.choose
  let δD := restrictionEvaluation.{c, v, max c v r} J B τ F σ α hα
  let a (n : ℕ) : G n ⋙ (L n).model.E ⟶ S.model.E ⋙ H n :=
    ((mateEquiv S.ordinaryAdjunction (L n).ordinaryAdjunction).symm
      (TwoSquare.mk _ _ _ _ (δ n).hom))
  have ha (n : ℕ) : IsIso (a n) := by
    exact sequenceScalarMate_isIso.{c, v, r} J
      (ring.{c, v, max c v r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ))
      (ring.{c, v, max c v r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J F σ)) n
      ((sheafCompose (coefficientSequenceTopology J)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
        (systemMap.{c, v, max c v r} J B τ F σ α hα))
      (ring J (B n)) (ring J (F n))
      (evaluation_ring.{c, v, max c v r} J B τ n)
      (evaluation_ring.{c, v, max c v r} J F σ n)
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map (α n))
      S.model.E (L n).model.E S.ordinaryAdjunction (L n).ordinaryAdjunction (δ n)
  let aD (n : ℕ) : e.{c, v, max c v r} J B τ n ⋙ (L n).T ⟶
      S.T ⋙ e.{c, v, max c v r} J F σ n :=
    ((mateEquiv S.adjunction (L n).adjunction).symm
      (TwoSquare.mk _ _ _ _ (δD n).hom))
  have hrep (n : ℕ) (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (R := systemRing.{c, v, max c v r} J B τ) P)
      (hp : CochainComplex.IsKFlatIndependentCoefficients (R := B n)
        (((G n).mapHomologicalComplex (.up ℤ)).obj P)) :
      (aD n).app (DerivedCategory.Q.obj P) ≫
          (e J F σ n).map (S.model.ε.app P) ≫
          (H n).mapDerivedCategoryFactors.hom.app
            ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P) =
        (L n).T.map ((G n).mapDerivedCategoryFactors.hom.app P) ≫
          (L n).model.ε.app (((G n).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (@asIso _ _ _ _ (a n) (ha n)) (.up ℤ)).hom.app P) := by
    refine mate_comparison_at
      (S.ordinaryAdjunction.mapHomologicalComplex (.up ℤ))
      ((L n).ordinaryAdjunction.mapHomologicalComplex (.up ℤ))
      S.adjunction (L n).adjunction S.model.ε (L n).model.ε
      R.mapDerivedCategoryFactors (Rn n).mapDerivedCategoryFactors
      (G n).mapDerivedCategoryFactors (H n).mapDerivedCategoryFactors P
      ?_ ?_ (TwoSquare.mk _ _ _ _ ((δ n).hom.mapHomologicalComplex (.up ℤ)))
      (TwoSquare.mk _ _ _ _ (δD n).hom) ?_
      (NatIso.mapHomologicalComplex (@asIso _ _ _ _ (a n) (ha n)) (.up ℤ)).hom ?_
    · intro K f
      apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app K)).mp
      rw [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
      exact S.transpose_model P K hP f
    · intro K f
      apply (cancel_mono ((Rn n).mapDerivedCategoryFactors.hom.app K)).mp
      rw [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
      exact (L n).transpose_model _ K hp f
    · intro K
      exact exactSquare_fac (δ n) K
    · intro K
      apply HomologicalComplex.hom_ext
      intro i
      have hu := unit_mateEquiv_symm S.ordinaryAdjunction (L n).ordinaryAdjunction
        (TwoSquare.mk _ _ _ _ (δ n).hom) (K.X i)
      exact hu.symm
  have hi (n : ℕ) (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (R := systemRing.{c, v, max c v r} J B τ) P)
      (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
        (J := coefficientSequenceTopology J) (R := systemRing.{c, v, max c v r} J B τ) (P.X i)) :
      IsIso ((aD n).app (DerivedCategory.Q.obj P)) := by
    have hp := evaluation_preservesKFlat.{c, v, r} J B τ n P hP hf
    have := S.model.computes P hP
    have := (L n).model.computes _ hp
    have : IsIso ((aD n).app (DerivedCategory.Q.obj P) ≫
        (e J F σ n).map (S.model.ε.app P) ≫
        (H n).mapDerivedCategoryFactors.hom.app
          ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P)) := by
      rw [hrep n P hP hp]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((e J F σ n).map (S.model.ε.app P) ≫
        (H n).mapDerivedCategoryFactors.hom.app
          ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P))
  have hD (n : ℕ) : IsIso (aD n) := by
    have hX (X : DS.{c, v, max c v r} J B τ) : IsIso ((aD n).app X) := by
      let K := DerivedCategory.Q.objPreimage X
      obtain ⟨P, q, hP, hf, hq, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients
          (R := systemRing.{c, v, max c v r} J B τ) K
      have hflat (i : ℤ) : SheafOfModules.IsFlatOnSite
          (J := coefficientSequenceTopology J) (R := systemRing.{c, v, max c v r} J B τ) (P.X i) :=
        (exactFunctor _ _).prop_of_iso
          (SheafOfModules.siteSheafTensorRightIso _ (P.X i)).symm (hf i)
      have := hq
      let z : DerivedCategory.Q.obj P ≅ X :=
        asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso X
      exact (NatTrans.isIso_app_iff_of_iso (aD n) z).mp (hi n P hP hflat)
    exact NatIso.isIso_of_isIso_app (aD n)
  refine ⟨{ evaluation := fun n ↦ (@asIso _ _ _ _ (aD n) (hD n)).symm
            transpose_evaluation := ?_ }⟩
  intro n M N f
  exact (adjunctionMate_transpose S.adjunction (L n).adjunction
    (TwoSquare.mk _ _ _ _ (δD n).hom) M N f).symm

end WeilConjectures.SemilinearSections
