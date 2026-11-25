/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationOrdinaryCoherence
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedCore
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientScalarDerivedAdjunction
public import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.CompositeMate
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-!
# Derived extension and coherence relative to a strict evaluation adjunction

Source: Zheng, Construction 4.1, p. 21; Stacks Project, Tags 06XN, 0FND and 09T5.
(blueprint: lem-pur-coefficient-evaluation-derived-extension-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w d
open CategoryTheory CategoryTheory.Limits Opposite
private theorem derive_comparison
    {A B DA DB : Type*} [Category A] [Category B] [Category DA] [Category DB]
    (QA : A ⥤ DA) (QB : B ⥤ DB) (W : MorphismProperty B) [QB.IsLocalization W]
    {F H : A ⥤ B} {R U : B ⥤ A} {FD HD : DA ⥤ DB} {RD UD : DB ⥤ DA}
    (a : F ⊣ R) (c : H ⊣ U) (ad : FD ⊣ RD) (cd : HD ⊣ UD)
    (εF : QA ⋙ FD ⟶ F ⋙ QB) (εH : QA ⋙ HD ⟶ H ⋙ QB)
    (ρF : R ⋙ QA ≅ QB ⋙ RD) (ρH : U ⋙ QA ≅ QB ⋙ UD)
    (hF : ∀ P K (f : F.obj P ⟶ K),
      ad.homEquiv _ _ (εF.app P ≫ QB.map f) = QA.map (a.homEquiv _ _ f) ≫ ρF.hom.app K)
    (hH : ∀ P K (f : H.obj P ⟶ K),
      cd.homEquiv _ _ (εH.app P ≫ QB.map f) = QA.map (c.homEquiv _ _ f) ≫ ρH.hom.app K)
    (ν : F ≅ H) :
    ∃ i : FD ≅ HD, ∀ P, i.hom.app (QA.obj P) ≫ εH.app P =
      εF.app P ≫ QB.map (ν.hom.app P) := by
  let η := (conjugateIsoEquiv c a ν).symm
  let Ψ := Localization.fullyFaithfulWhiskeringLeft QB W DA
  let δ := Ψ.preimageIso
    (ρF.symm ≪≫ Functor.isoWhiskerRight η QA ≪≫ ρH)
  have hδ (K : B) : ρF.hom.app K ≫ δ.hom.app (QB.obj K) =
      QA.map (η.hom.app K) ≫ ρH.hom.app K := by
    have h := congr_app (Ψ.map_preimage
      (ρF.symm ≪≫ Functor.isoWhiskerRight η QA ≪≫ ρH).hom) K
    change δ.hom.app (QB.obj K) = _ at h
    rw [h]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, ← Category.assoc,
      Iso.hom_inv_id_app, Category.id_comp]
  have hν (P : A) : a.homEquiv _ _ (ν.hom.app P) ≫
      η.hom.app (H.obj P) = c.unit.app P := by
    apply (cancel_mono ((conjugateIsoEquiv c a ν).hom.app (H.obj P))).1
    simp only [Category.assoc, η, Iso.symm_hom, Iso.inv_hom_id_app,
      Category.comp_id]
    exact (unit_conjugateEquiv c a ν.hom P).symm
  refine ⟨(ad.ofNatIsoRight δ).leftAdjointUniq cd, ?_⟩
  exact normalizedAdjunction_uniqueness a c ad cd εF.app εH.app
    ρF.hom.app ρH.hom.app hF hH η δ ν.hom.app hν hδ

private theorem scalar_composition
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    {E₁ : A ⥤ B} {R₁ : B ⥤ A} {E₂ : B ⥤ C} {R₂ : C ⥤ B}
    {E₃ : A ⥤ C} {R₃ : C ⥤ A}
    [E₁.Additive] [R₁.Additive] [E₂.Additive] [R₂.Additive]
    [E₃.Additive] [R₃.Additive]
    {a₁ : E₁ ⊣ R₁} {a₂ : E₂ ⊣ R₂} {a₃ : E₃ ⊣ R₃}
    {P₁ : CochainComplex A ℤ → Prop} {P₂ : CochainComplex B ℤ → Prop}
    {P₃ : CochainComplex A ℤ → Prop}
    (D₁ : SheafOfModules.DerivedCoefficientScalarExtension E₁ R₁ a₁ P₁)
    (D₂ : SheafOfModules.DerivedCoefficientScalarExtension E₂ R₂ a₂ P₂)
    (D₃ : SheafOfModules.DerivedCoefficientScalarExtension E₃ R₃ a₃ P₃)
    (ν : E₁ ⋙ E₂ ≅ E₃) :
    ∃ i : D₁.derived ⋙ D₂.derived ≅ D₃.derived, ∀ P,
      i.hom.app (DerivedCategory.Q.obj P) ≫ D₃.counit.app P =
        D₂.derived.map (D₁.counit.app P) ≫
          D₂.counit.app ((E₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso ν (.up ℤ)).hom.app P) := by
  let E₁c := E₁.mapHomologicalComplex (.up ℤ)
  let E₂c := E₂.mapHomologicalComplex (.up ℤ)
  let R₁c := R₁.mapHomologicalComplex (.up ℤ)
  let R₂c := R₂.mapHomologicalComplex (.up ℤ)
  let ε : DerivedCategory.Q ⋙ (D₁.derived ⋙ D₂.derived) ⟶
      (E₁c ⋙ E₂c) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight D₁.counit D₂.derived ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft E₁c D₂.counit ≫
      (Functor.associator _ _ _).inv
  let ρ : (R₂c ⋙ R₁c) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ (D₂.restriction ⋙ D₁.restriction) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R₂c D₁.restrictionFactors.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight D₂.restrictionFactors.symm D₁.restriction ≪≫
      Functor.associator _ _ _
  have hc := normalizedAdjunction_composition
    (a₁.mapHomologicalComplex (.up ℤ)) (a₂.mapHomologicalComplex (.up ℤ))
    D₁.derivedAdj D₂.derivedAdj D₁.counit D₂.counit
    D₁.restrictionFactors.inv D₂.restrictionFactors.inv D₁.transpose D₂.transpose
  obtain ⟨i, hi⟩ := derive_comparison DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
    ((a₁.mapHomologicalComplex (.up ℤ)).comp (a₂.mapHomologicalComplex (.up ℤ)))
    (a₃.mapHomologicalComplex (.up ℤ))
    (D₁.derivedAdj.comp D₂.derivedAdj) D₃.derivedAdj ε D₃.counit
    ρ D₃.restrictionFactors.symm
    (by
      intro P K f
      dsimp only [E₁c, R₁c, R₂c, ε, ρ]
      simpa only [ε, ρ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id, Category.assoc, Category.id_comp] using hc P K f)
    D₃.transpose (Functor.mapHomologicalComplexCompIso ν (.up ℤ))
  refine ⟨i, ?_⟩
  intro P
  simpa only [ε, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hi P

private theorem resolving_natTrans_ext
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A] [Category B]
    (P : CochainComplex A ℤ → Prop)
    (hres : ∀ X, ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X), P Y ∧ QuasiIso s)
    {F G : DerivedCategory A ⥤ B} (τ τ' : F ⟶ G)
    (h : ∀ X, P X → τ.app (DerivedCategory.Q.obj X) = τ'.app (DerivedCategory.Q.obj X)) :
    τ = τ' := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro X
  obtain ⟨Y, s, hY, hs⟩ := hres X
  let := hs
  apply (cancel_epi (F.map (DerivedCategory.Q.map s))).1
  rw [τ.naturality, τ'.naturality, h Y hY]

namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]

local notation "ev" => coefficientEvaluation (J := J) (O := O) (ell := ell)
local notation "tensor" => coefficientTensor (J := J) (O := O) (ell := ell)
local notation "tensorAdj" => coefficientTensorAdj (J := J) (O := O) (ell := ell)

/-- The truncation map is constructed as the mate of the derived system transition.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-extension-coherence). -/
def coefficientEvaluationSigma
    {ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell)}
    [∀ n, (ordinary.extension n).Additive]
    (scalar : CoefficientScalarDerivedAssignment (J := J) (O := O) (ell := ell))
    (core : CoefficientEvaluationDerivedCoreData ordinary)
    (transition : ∀ {m n : ℕ} (h : n ≤ m),
      core.evaluation m ⟶ core.evaluation n ⋙ (scalar h).restriction)
    {m n : ℕ} (h : n ≤ m) : (scalar h).derived ⋙ core.derivedExtension n ⟶
      core.derivedExtension m :=
  CategoryTheory.Adjunction.compositeMate
    (core.derivedAdj n) (core.derivedAdj m) (scalar h).derivedAdj (transition h)

attribute [local irreducible] coefficientEvaluationSigma

/-- Index coherence for fixed strict, scalar-derived and evaluation-derived adjunctions.
All adjunctions, their universal comparisons and their normalized representative
transposes have already been constructed.
Source: Zheng, Construction 4.1, p. 21; Stacks 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-extension-coherence). -/
structure CoefficientEvaluationDerivedCoherenceData
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive]
    (scalar : CoefficientScalarDerivedAssignment (J := J) (O := O) (ell := ell))
    (core : CoefficientEvaluationDerivedCoreData ordinary)
    (transition : ∀ {m n : ℕ} (h : n ≤ m),
      core.evaluation m ⟶ core.evaluation n ⋙ (scalar h).restriction)
    (strict : CoefficientEvaluationOrdinaryCoherenceData ordinary)
    (unit : ∀ n, (scalar (Nat.le_refl n)).derived ≅ 𝟭 _) where
  sigma_rep : ∀ {m n} (h : n ≤ m) P,
    (CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := J) O ell m)) P →
    (∀ i, (IsFlatOnSite (R := coefficientQuotientSheaf (J := J) O ell m)) (P.X i)) →
    (coefficientEvaluationSigma scalar core transition h).app (DerivedCategory.Q.obj P) ≫
      (core.counit m).app P =
      (core.derivedExtension n).map ((scalar h).counit.app P) ≫
        (core.counit n).app (((tensor h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (strict.strictSigmaComplex h P)
  derivedAssoc : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m),
    (scalar h₁).derived ⋙ (scalar h₂).derived ≅ (scalar (h₂.trans h₁)).derived
  derivedAssoc_rep : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) P,
    (CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := J) O ell l)) P →
    (∀ i, (IsFlatOnSite (R := coefficientQuotientSheaf (J := J) O ell l)) (P.X i)) →
    (derivedAssoc h₁ h₂).hom.app (DerivedCategory.Q.obj P) ≫
      (scalar (h₂.trans h₁)).counit.app P =
    (scalar h₂).derived.map ((scalar h₁).counit.app P) ≫
      (scalar h₂).counit.app
        (((tensor h₁).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (strict.tensorAssocComplex h₁ h₂ P).hom
  sigma_id : ∀ n N, (coefficientEvaluationSigma scalar core transition (Nat.le_refl n)).app N =
    (core.derivedExtension n).map ((unit n).hom.app N)
  sigma_comp : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) N,
    (coefficientEvaluationSigma scalar core transition h₂).app ((scalar h₁).derived.obj N) ≫
      (coefficientEvaluationSigma scalar core transition h₁).app N =
      (core.derivedExtension n).map ((derivedAssoc h₁ h₂).hom.app N) ≫
        (coefficientEvaluationSigma scalar core transition (h₂.trans h₁)).app N

omit [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)] in
private theorem ordinary_unit
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive]
    (strict : CoefficientEvaluationOrdinaryCoherenceData ordinary) (n : ℕ)
    (P : coefficientLevelModules (J := J) O ell n) :
    (strict.strictSigma (Nat.le_refl n)).app P =
      (ordinary.extension n).map ((strict.tensorUnit n).hom.app P) := by
  apply ((ordinary.adj n).homEquiv _ _).injective
  rw [strict.strictSigma_transpose, Adjunction.homEquiv_unit]
  erw [← (ordinary.adj n).unit.naturality]
  apply ((tensorAdj (Nat.le_refl n)).homEquiv _ _).injective
  have ht := ordinary.hom_formula (Nat.le_refl n) P ((ordinary.extension n).obj P) (𝟙 _)
  simp only [CategoryTheory.Functor.map_id, Adjunction.homEquiv_id] at ht
  erw [ht]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  have hu := congrArg (fun f ↦ (f.hom.app U) x) (strict.tensorUnit_normalized n P)
  change ((strict.tensorUnit n).hom.app P).val.app U
    (((tensorAdj (Nat.le_refl n)).unit.app P).val.app U x) = x at hu
  have hi := congrArg (fun f ↦ (f.hom.app U)
    (((ordinary.adj n).unit.app P).val.app U x))
      (ordinary.transitionsNormalized.1 n ((ordinary.extension n).obj P))
  change ((ordinary.strictTransition (Nat.le_refl n)).app _).val.app U
    (((ordinary.adj n).unit.app P).val.app U x) = _ at hi
  rw [Adjunction.homEquiv_unit]
  change _ = ((ordinary.adj n).unit.app P).val.app U
    (((strict.tensorUnit n).hom.app P).val.app U
      (((tensorAdj (Nat.le_refl n)).unit.app P).val.app U x))
  rw [hu]
  exact hi

omit [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)] in
private theorem ordinary_comp
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive]
    (strict : CoefficientEvaluationOrdinaryCoherenceData ordinary)
    {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m)
    (P : coefficientLevelModules (J := J) O ell l) :
    (strict.strictSigma h₂).app ((tensor h₁).obj P) ≫
      (strict.strictSigma h₁).app P =
    (ordinary.extension n).map ((strict.tensorAssoc h₁ h₂).hom.app P) ≫
      (strict.strictSigma (h₂.trans h₁)).app P := by
  apply ((ordinary.adj n).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, strict.strictSigma_transpose,
    Adjunction.homEquiv_naturality_left, strict.strictSigma_transpose]
  apply (cancel_mono ((ordinary.below (h₂.trans h₁)).hom.app P)).1
  erw [strict.strictSigma_below h₁ h₂ P]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem sigma_representative
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive]
    (scalar : CoefficientScalarDerivedAssignment (J := J) (O := O) (ell := ell))
    (core : CoefficientEvaluationDerivedCoreData ordinary)
    (transition : ∀ {m n : ℕ} (h : n ≤ m),
      core.evaluation m ⟶ core.evaluation n ⋙ (scalar h).restriction)
    (strict : CoefficientEvaluationOrdinaryCoherenceData ordinary)
    (transition_rep : ∀ {m n} (h : n ≤ m) K,
      (transition h).app (DerivedCategory.Q.obj K) ≫
        (scalar h).restriction.map ((core.evaluationFactors n).hom.app K) ≫
        (scalar h).restrictionFactors.hom.app
          (((ev n).mapHomologicalComplex (.up ℤ)).obj K) =
      (core.evaluationFactors m).hom.app K ≫ DerivedCategory.Q.map
        (((ordinary.strictTransition h).mapHomologicalComplex (.up ℤ)).app K))
    {m n : ℕ} (h : n ≤ m) (P : CochainComplex (coefficientLevelModules (J := J) O ell m) ℤ) :
    (coefficientEvaluationSigma scalar core transition h).app (DerivedCategory.Q.obj P) ≫
        (core.counit m).app P =
      (core.derivedExtension n).map ((scalar h).counit.app P) ≫
        (core.counit n).app (((tensor h).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (strict.strictSigmaComplex h P) := by
  have hf : ((ordinary.adj n).mapHomologicalComplex (.up ℤ)).homEquiv
      (((tensor h).mapHomologicalComplex (.up ℤ)).obj P)
      (((ordinary.extension m).mapHomologicalComplex (.up ℤ)).obj P)
      (strict.strictSigmaComplex h P) =
      (NatIso.mapHomologicalComplex (ordinary.below h) (.up ℤ)).inv.app P := by
    rw [Adjunction.homEquiv_unit]
    ext i : 1
    change (ordinary.adj n).unit.app
        ((((tensor h).mapHomologicalComplex (.up ℤ)).obj P).X i) ≫
      (ev n).map ((strict.strictSigmaComplex h P).f i) = _
    rw [strict.strictSigmaComplex_f]
    exact strict.strictSigma_transpose h (P.X i)
  have hu : ((tensorAdj h).mapHomologicalComplex (.up ℤ)).homEquiv P _
      ((NatIso.mapHomologicalComplex (ordinary.below h) (.up ℤ)).inv.app P) =
      ((ordinary.adj m).mapHomologicalComplex (.up ℤ)).unit.app P ≫
        ((ordinary.strictTransition h).mapHomologicalComplex (.up ℤ)).app
          (((ordinary.extension m).mapHomologicalComplex (.up ℤ)).obj P) := by
    rw [Adjunction.homEquiv_unit]
    ext i : 1
    change (tensorAdj h).unit.app (P.X i) ≫
      (coefficientRestriction O ell h).map ((ordinary.below h).inv.app (P.X i)) =
      (ordinary.adj m).unit.app (P.X i) ≫
        (ordinary.strictTransition h).app ((ordinary.extension m).obj (P.X i))
    have hh := ordinary.hom_formula h (P.X i)
      ((((ordinary.extension m).mapHomologicalComplex (.up ℤ)).obj P).X i) (𝟙 _)
    erw [(ev n).map_id, Category.comp_id, Adjunction.homEquiv_id,
      Adjunction.homEquiv_unit] at hh
    exact hh
  apply ((core.derivedAdj n).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  dsimp only [Functor.comp_obj]
  erw [core.transpose n (((tensor h).mapHomologicalComplex (.up ℤ)).obj P)
    (((ordinary.extension m).mapHomologicalComplex (.up ℤ)).obj P)
    (strict.strictSigmaComplex h P), hf]
  unfold coefficientEvaluationSigma
  rw [Adjunction.compositeMate_homEquiv]
  apply ((scalar h).derivedAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
  have hc := core.transpose m P
    (((ordinary.extension m).mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id] at hc
  erw [hc]
  rw [Adjunction.homEquiv_naturality_right, CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, ← Adjunction.homEquiv_naturality_right]
  erw [(scalar h).transpose, hu, DerivedCategory.Q.map_comp]
  apply (cancel_mono ((scalar h).restriction.map
    ((core.evaluationFactors n).hom.app
      (((ordinary.extension m).mapHomologicalComplex (.up ℤ)).obj P)))).1
  apply (cancel_mono ((scalar h).restrictionFactors.hom.app
    (((ev n).mapHomologicalComplex (.up ℤ)).obj
      (((ordinary.extension m).mapHomologicalComplex (.up ℤ)).obj P)))).1
  simp only [Category.assoc]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [transition_rep]
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id, Category.assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_comp]
  erw [Category.id_comp, Category.comp_id]

/-- Derived compatibility of the strict truncation inclusions, with identity and
composition laws for their adjunction mates.
Source: Zheng, Construction 4.1, p. 21; Stacks Tags 06XN, 0FND and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-extension-coherence).
Proof: scalar extension takes flat-term K-flat complexes to flat-term K-flat complexes.
For such a complex P, transpose the proposed sigma representative equation first under
the normalized evaluation adjunction and then under the normalized scalar adjunction.
Their representative formulas and the transition's localization equation reduce both
sides to the ordinary extension Hom formula and the strict truncation's transpose.
Injectivity of the two Hom bijections proves the sigma comparison.
On a flat-term K-flat P define the derived associator by the composite of the second
derived tensor applied to the first counit, the second counit at the first tensor of P,
the localization of the ordinary associator, and the inverse direct tensor counit.
All these maps are isomorphisms: the first and direct counits compute on P, and the
second computes because scalar extension preserves the resolving class. Naturality of
these counits and of the ordinary associator gives naturality on resolving complexes.
Pass to their homotopy classes. Every homotopy object admits a resolving complex, and
the calculus of quasi-isomorphism fractions gives common resolving refinements. Thus
the same formula is independent of the chosen resolution and descends naturally to
the derived categories. The inverse formula, using the inverse ordinary associator,
gives its inverse. Its defining equation is exactly derivedAssoc_rep. Any other
comparison with that equation agrees after canceling the invertible direct counit on
each resolving complex, hence agrees on every derived object.
For the identity index, the ordinary tensor unit normalization and strict Hom formula
identify the strict truncation with extension applied to the ordinary tensor unit.
For three indices, evaluate the two successive strict truncations at q. Below the
smallest index, transpose by the three scalar Hom bijections. Tensor unit normalization
reduces both values to the same product of scalar factors; above it the source is zero.
The faithful component evaluations therefore give the strict composition identity.
Apply the sigma representative comparison to these ordinary identities and insert the
derived unit and associator comparison equations. On a flat-term K-flat resolution all
universal counits in these equations are invertible, including those after a scalar
extension, so cancellation gives sigma_id and sigma_comp on its localized object.
Every derived object is isomorphic to one of these objects. Naturality along that
isomorphism proves both laws on every derived object. No flatness of quotient maps is
assumed. -/
theorem coefficientEvaluationDerivedCoherence
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive]
    (scalar : CoefficientScalarDerivedAssignment (J := J) (O := O) (ell := ell))
    (core : CoefficientEvaluationDerivedCoreData ordinary)
    (transition : ∀ {m n : ℕ} (h : n ≤ m),
      core.evaluation m ⟶ core.evaluation n ⋙ (scalar h).restriction)
    (strict : CoefficientEvaluationOrdinaryCoherenceData ordinary)
    (unit : ∀ n, (scalar (Nat.le_refl n)).derived ≅ 𝟭 _)
    (unit_rep : ∀ n P,
      (unit n).hom.app (DerivedCategory.Q.obj P) =
        (scalar (Nat.le_refl n)).counit.app P ≫
          DerivedCategory.Q.map (strict.tensorUnitComplex n P).hom)
    (transition_rep : ∀ {m n} (h : n ≤ m) K,
    (transition h).app (DerivedCategory.Q.obj K) ≫
      (scalar h).restriction.map ((core.evaluationFactors n).hom.app K) ≫
      (scalar h).restrictionFactors.hom.app
        (((ev n).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (core.evaluationFactors m).hom.app K ≫
        DerivedCategory.Q.map
          (((ordinary.strictTransition h).mapHomologicalComplex (ComplexShape.up ℤ)).app K)) :
    Nonempty
      (CoefficientEvaluationDerivedCoherenceData ordinary scalar core transition strict unit) := by
  classical
  have hs := fun {m n : ℕ} (h : n ≤ m) P ↦
    sigma_representative ordinary scalar core transition strict transition_rep h P
  have hc (l m n : ℕ) (h₁ : m ≤ l) (h₂ : n ≤ m) :=
    scalar_composition (scalar h₁) (scalar h₂) (scalar (h₂.trans h₁))
      (strict.tensorAssoc h₁ h₂)
  choose assoc ha using hc
  have har {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m) P :
      (assoc l m n h₁ h₂).hom.app (DerivedCategory.Q.obj P) ≫
        (scalar (h₂.trans h₁)).counit.app P =
      (scalar h₂).derived.map ((scalar h₁).counit.app P) ≫
        (scalar h₂).counit.app (((tensor h₁).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (strict.tensorAssocComplex h₁ h₂ P).hom := by
    rw [ha]
    congr 2
    apply congrArg
    apply HomologicalComplex.hom_ext
    intro i
    exact (strict.tensorAssocComplex_f h₁ h₂ P i).symm
  have res (n : ℕ) (X : CochainComplex (coefficientLevelModules (J := J) O ell n) ℤ) :
      ∃ (Y : CochainComplex (coefficientLevelModules (J := J) O ell n) ℤ) (s : Y ⟶ X),
        Y.IsKFlatIndependentCoefficients ∧ QuasiIso s := by
    obtain ⟨Y, s, hY, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X
    exact ⟨Y, s, hY, hs⟩
  refine ⟨{
    sigma_rep := fun h P _ _ ↦ hs h P
    derivedAssoc := fun h₁ h₂ ↦ assoc _ _ _ h₁ h₂
    derivedAssoc_rep := fun h₁ h₂ P _ _ ↦ har h₁ h₂ P
    sigma_id := ?_
    sigma_comp := ?_ }⟩
  · intro n N
    let τ := coefficientEvaluationSigma scalar core transition (Nat.le_refl n)
    let τ' : (scalar (Nat.le_refl n)).derived ⋙ core.derivedExtension n ⟶
        core.derivedExtension n := Functor.whiskerRight (unit n).hom (core.derivedExtension n)
    have ht : τ = τ' := by
      apply resolving_natTrans_ext _ (res n)
      intro P hP
      let := core.computes n P hP
      apply (cancel_mono ((core.counit n).app P)).1
      change τ.app _ ≫ _ = (core.derivedExtension n).map ((unit n).hom.app _) ≫ _
      rw [unit_rep, CategoryTheory.Functor.map_comp, Category.assoc]
      erw [(core.counit n).naturality ((strict.tensorUnitComplex n P).hom)]
      rw [hs]
      congr 2
      change DerivedCategory.Q.map (strict.strictSigmaComplex (Nat.le_refl n) P) =
        DerivedCategory.Q.map (((ordinary.extension n).mapHomologicalComplex (.up ℤ)).map
          (strict.tensorUnitComplex n P).hom)
      congr 1
      apply HomologicalComplex.hom_ext
      intro i
      rw [strict.strictSigmaComplex_f]
      change _ = (ordinary.extension n).map (((strict.tensorUnitComplex n P).hom).f i)
      rw [strict.tensorUnitComplex_f]
      exact ordinary_unit ordinary strict n (P.X i)
    exact congr_app ht N
  · intro l m n h₁ h₂ N
    let τ : ((scalar h₁).derived ⋙ (scalar h₂).derived) ⋙ core.derivedExtension n ⟶
        core.derivedExtension l :=
      Functor.whiskerLeft (scalar h₁).derived
        (coefficientEvaluationSigma scalar core transition h₂) ≫
        coefficientEvaluationSigma scalar core transition h₁
    let τ' : ((scalar h₁).derived ⋙ (scalar h₂).derived) ⋙ core.derivedExtension n ⟶
        core.derivedExtension l :=
      Functor.whiskerRight (assoc l m n h₁ h₂).hom (core.derivedExtension n) ≫
        coefficientEvaluationSigma scalar core transition (h₂.trans h₁)
    have ht : τ = τ' := by
      apply resolving_natTrans_ext _ (res l)
      intro P hP
      let := core.computes l P hP
      apply (cancel_mono ((core.counit l).app P)).1
      dsimp only [τ, τ', NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app]
      rw [Category.assoc, hs h₁ P, Category.assoc, hs (h₂.trans h₁) P]
      rw [← CategoryTheory.Functor.map_comp_assoc, har, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp]
      rw [← (coefficientEvaluationSigma scalar core transition h₂).naturality_assoc]
      simp only [Category.assoc]
      erw [← Category.assoc ((coefficientEvaluationSigma scalar core transition h₂).app _)
        ((core.counit m).app _) _, hs h₂
          (((tensor h₁).mapHomologicalComplex (.up ℤ)).obj P)]
      simp only [Category.assoc]
      erw [(core.counit n).naturality_assoc]
      simp only [Functor.comp_map, ← DerivedCategory.Q.map_comp]
      congr 2
      apply congrArg
      apply congrArg
      apply HomologicalComplex.hom_ext
      intro i
      simp only [HomologicalComplex.comp_f, strict.strictSigmaComplex_f]
      change _ = (ordinary.extension n).map
        (((strict.tensorAssocComplex h₁ h₂ P).hom).f i) ≫ _
      rw [strict.tensorAssocComplex_f]
      exact ordinary_comp ordinary strict h₁ h₂ (P.X i)
    exact congr_app ht N

end SheafOfModules
