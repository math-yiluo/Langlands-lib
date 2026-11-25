/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarModel
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Exact-functor factorizations for constant scalar models

Source: Stacks Project, Tags 05RU, 093J, 093M and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] completedAdicChangeData completedAdicScalar completedAdicRing
  Functor.mapDerivedCategory HasDerivedCategory.standard Functor.leftAdjoint

private theorem squareSymm
    {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory E]
    {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    mapDerivedCategorySquareIso e.symm = (mapDerivedCategorySquareIso e).symm := by
  apply Iso.ext
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, mapDerivedCategoryNatIso_symm, Category.assoc]
private theorem pasteAssoc
    {C₀ D₀ C₁ D₁ C₂ D₂ E : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    [Category C₂] [Category D₂] [Category E]
    {R₀ : C₀ ⥤ D₀} {L₁ : C₀ ⥤ C₁} {H₁ : D₀ ⥤ D₁} {R₁ : C₁ ⥤ D₁}
    {L₂ : C₁ ⥤ C₂} {H₂ : D₁ ⥤ D₂} {R₂ : C₂ ⥤ D₂}
    {H₃ : D₂ ⥤ E} {L₃ : C₂ ⥤ E}
    (e₁ : R₀ ⋙ H₁ ≅ L₁ ⋙ R₁) (e₂ : R₁ ⋙ H₂ ≅ L₂ ⋙ R₂)
    (z : R₂ ⋙ H₃ ≅ L₃) :
    finitePerfectAdicPasteCoefficientStep e₁ (finitePerfectAdicPasteCoefficientStep e₂ z) =
      finitePerfectAdicPasteCoefficientStep (R := R₀) (H := H₁ ⋙ H₂)
        (L := L₁ ⋙ L₂) (S := R₂) (P := H₃) (Q := L₃)
        (finitePerfectAdicPasteCoefficientStep (L := L₁) (S := R₁) e₁ e₂) z := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [finitePerfectAdicPasteCoefficientStep, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc]
private theorem pasteAssociators
    {C₀ D₀ C₁ D₁ C₂ D₂ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    {R₀ : C₀ ⥤ D₀} {L₁ : C₀ ⥤ C₁} {H₁ : D₀ ⥤ D₁} {R₁ : C₁ ⥤ D₁}
    {L₂ : C₁ ⥤ C₂} {H₂ : D₁ ⥤ D₂} {R₂ : C₂ ⥤ D₂}
    (e₁ : R₀ ⋙ H₁ ≅ L₁ ⋙ R₁) (e₂ : R₁ ⋙ H₂ ≅ L₂ ⋙ R₂) :
    (associator R₀ H₁ H₂).symm ≪≫ isoWhiskerRight e₁ H₂ ≪≫
      associator L₁ R₁ H₂ ≪≫ isoWhiskerLeft L₁ e₂ ≪≫
        (associator L₁ L₂ R₂).symm = finitePerfectAdicPasteCoefficientStep e₁ e₂ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [finitePerfectAdicPasteCoefficientStep, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, associator_hom_app, associator_inv_app, Category.id_comp,
    Category.comp_id]

private theorem localizedPaste
    {C D E E' F : Type*}
    [Category C] [Category D] [Category E] [Category E'] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian E'] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory E'] [HasDerivedCategory F]
    {R : C ⥤ D} {L : C ⥤ E'} {H : D ⥤ E} {S : E' ⥤ E}
    {P : E ⥤ F} {Q : E' ⥤ F}
    [R.Additive] [L.Additive] [H.Additive] [S.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (e : R ⋙ H ≅ L ⋙ S) (z : S ⋙ P ≅ Q)
    {J : DerivedCategory E ⥤ DerivedCategory F}
    {K : DerivedCategory E' ⥤ DerivedCategory F}
    (a : P.mapDerivedCategory ≅ J) (b : Q.mapDerivedCategory ≅ K)
    (w : S.mapDerivedCategory ⋙ J ≅ K)
    (hw : (mapDerivedCategoryCompIso S P).inv ≫
      whiskerLeft S.mapDerivedCategory a.hom ≫ w.hom =
      (mapDerivedCategoryNatIso z).hom ≫ b.hom) :
    (mapDerivedCategoryCompIso R (H ⋙ P)).inv ≫
      whiskerLeft R.mapDerivedCategory
        ((mapDerivedCategoryCompIso H P).symm ≪≫ isoWhiskerLeft H.mapDerivedCategory a).hom ≫
      (finitePerfectAdicPasteCoefficientStep (mapDerivedCategorySquareIso e) w).hom =
    (mapDerivedCategoryNatIso (finitePerfectAdicPasteCoefficientStep e z)).hom ≫
      ((mapDerivedCategoryCompIso L Q).symm ≪≫ isoWhiskerLeft L.mapDerivedCategory b).hom := by
  simp only [finitePerfectAdicPasteCoefficientStep, Iso.trans_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, Iso.symm_hom]
  apply NatTrans.ext
  funext M
  have hRH := NatTrans.congr_app (mapDerivedCategoryCompIso_assoc R H P) M
  have hLS := NatTrans.congr_app (mapDerivedCategoryCompIso_assoc L S P) M
  have he := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerRight e P) M
  have hz := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft L z) M
  have hwM := NatTrans.congr_app hw (L.mapDerivedCategory.obj M)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.comp_obj] at hRH hLS he hz hwM ⊢
  have hn := a.hom.naturality ((mapDerivedCategorySquareIso e).hom.app M)
  simp only [Functor.comp_obj, mapDerivedCategorySquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app] at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn.symm]
  rw [← Category.assoc, hRH, Category.assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← P.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [P.mapDerivedCategory.map_id, Category.id_comp]
  rw [← reassoc_of% he, ← reassoc_of% hLS, hwM,
    ← reassoc_of% hz]
  simp only [mapDerivedCategoryNatIso_trans, NatTrans.comp_app, Category.assoc]

variable (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
  (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
  (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ)

/-- The derived constant quotient source before evaluating a complex.
Source: Stacks Tags 093J and 05RU. -/
def finitePerfectAdicScalarModelSource :=
  finitePerfectAdicAlgebraLift (A ⧸ d.ideal ^ (n + 1)) ⋙
    normalizationConstant V.left.smallEtaleTopology ⋙
    localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))) ⋙
    finitePerfectAdicScalarRealization X d V U W f n

instance finitePerfectAdicOrdinaryScalarSource_additive :
    (finitePerfectAdicOrdinaryScalarSource X d V U W f n).Additive :=
  (finitePerfectAdicOrdinaryScalarSource_exact X d V U W f n).1
instance finitePerfectAdicOrdinaryScalarSource_limits :
    PreservesFiniteLimits (finitePerfectAdicOrdinaryScalarSource X d V U W f n) :=
  (finitePerfectAdicOrdinaryScalarSource_exact X d V U W f n).2.1
instance finitePerfectAdicOrdinaryScalarSource_colimits :
    PreservesFiniteColimits (finitePerfectAdicOrdinaryScalarSource X d V U W f n) :=
  (finitePerfectAdicOrdinaryScalarSource_exact X d V U W f n).2.2
instance finitePerfectAdicOrdinaryScalarTarget_additive :
    (finitePerfectAdicOrdinaryScalarTarget X d W n).Additive :=
  (finitePerfectAdicOrdinaryScalarTarget_exact X d W n).1
instance finitePerfectAdicOrdinaryScalarTarget_limits :
    PreservesFiniteLimits (finitePerfectAdicOrdinaryScalarTarget X d W n) :=
  (finitePerfectAdicOrdinaryScalarTarget_exact X d W n).2.1
instance finitePerfectAdicOrdinaryScalarTarget_colimits :
    PreservesFiniteColimits (finitePerfectAdicOrdinaryScalarTarget X d W n) :=
  (finitePerfectAdicOrdinaryScalarTarget_exact X d W n).2.2

/-- Compose the canonical exact-functor factorization with a specified factorization.
Source: Stacks Tag 05RU, compatibility of exact localization with composition. -/
def finitePerfectAdicDerivedFactor
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {J : DerivedCategory D ⥤ DerivedCategory E} (e : G.mapDerivedCategory ≅ J) :
    (F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ J :=
  (mapDerivedCategoryCompIso F G).symm ≪≫ isoWhiskerLeft F.mapDerivedCategory e

/-- The source is the exact derived functor of its explicit ordinary composite.
Source: Stacks Tag 05RU; exact derived functors commute with composition. -/
def finitePerfectAdicScalarModelSourceFactors :
    (finitePerfectAdicOrdinaryScalarSource X d V U W f n).mapDerivedCategory ≅
      finitePerfectAdicScalarModelSource X d V U W f n := by
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).1
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).2.1
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).2.2
  let B := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
  let L := finitePerfectAdicScalarModelLift (A ⧸ d.ideal ^ (n + 1))
  let C := constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} B)
  let P := ProEtale.comparisonUpperStar (ModuleCat.{t + 1} B) V.left
  let R := ProEtale.upperStar (ModuleCat.{t + 1} B) U.hom
  let S := finitePerfectAdicScalarModules X d V U W f n
  exact finitePerfectAdicDerivedFactor L (C ⋙ P ⋙ R ⋙ S)
    (finitePerfectAdicDerivedFactor C (P ⋙ R ⋙ S)
      (finitePerfectAdicDerivedFactor P (R ⋙ S)
        (finitePerfectAdicDerivedFactor R S (Iso.refl S.mapDerivedCategory))))

instance finitePerfectAdicScalarModelExtension_limits :
    PreservesFiniteLimits (completedAdicScalarExtension X d) :=
  (finitePerfectAdicScalarModelExtension_exact X d).1
instance finitePerfectAdicScalarModelExtension_colimits :
    PreservesFiniteColimits (completedAdicScalarExtension X d) :=
  (finitePerfectAdicScalarModelExtension_exact X d).2

/-- Ordinary completed realization is left exact. Source: Stacks Tags 093J and 093M. -/
instance finitePerfectAdicScalarModelOrdinary_limits :
    PreservesFiniteLimits (finitePerfectAdicScalarModelOrdinary X d) := by
  have := (finitePerfectAdicConstant_exact X A).2.1
  unfold finitePerfectAdicScalarModelOrdinary
  infer_instance

/-- Ordinary completed realization is right exact. Source: Stacks Tags 093J and 093M. -/
instance finitePerfectAdicScalarModelOrdinary_colimits :
    PreservesFiniteColimits (finitePerfectAdicScalarModelOrdinary X d) := by
  have := (finitePerfectAdicConstant_exact X A).2.2
  unfold finitePerfectAdicScalarModelOrdinary
  infer_instance

/-- Compare an exact functor's localization with a specified universal left derived pair.
Source: Stacks Tag 05RU; uniqueness of left derived functors. -/
def finitePerfectAdicExactDerivedIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ⥤ D) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (T : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ T ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    E.mapDerivedCategory ≅ T := by
  have : E.mapDerivedCategory.IsLeftDerivedFunctor E.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso C (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ E.mapDerivedCategoryFactorsh
  exact (Functor.leftDerivedUnique E.mapDerivedCategory T ε E.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso C (.up ℤ))).symm

/-- Exact ordinary extension and the specified total derived extension agree.
Source: Stacks Tags 093M and 05RU; uniqueness of the left derived pair. -/
def finitePerfectAdicScalarModelCompletedFactors :
    (finitePerfectAdicScalarModelOrdinary X d).mapDerivedCategory ≅
      finitePerfectAdicDerivedConstant X A ⋙
        completedAdicDerivedChange X (completedAdicScalar X d) := by
  have := (finitePerfectAdicConstant_exact X A).1
  have := (finitePerfectAdicConstant_exact X A).2.1
  have := (finitePerfectAdicConstant_exact X A).2.2
  let E := completedAdicScalarExtension X d
  let h := (completedAdicScalarExtensionData X d).choose_spec.choose_spec.choose_spec
    |>.choose_spec.2.2
  let T := h.choose
  let ε := h.choose_spec.choose
  have hε := h.choose_spec.choose_spec.1
  have : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) := hε
  let e := finitePerfectAdicExactDerivedIso E T ε
  exact (mapDerivedCategoryCompIso (finitePerfectAdicConstant X A) E).symm ≪≫
    isoWhiskerLeft (finitePerfectAdicDerivedConstant X A) e

/-- The completed ordinary target localizes to the model's specified local realization.
Source: Stacks Tags 05RU and 03DJ. -/
def finitePerfectAdicScalarModelTargetFactors :
    (finitePerfectAdicOrdinaryScalarTarget X d W n).mapDerivedCategory ≅
      DerivedCategory.adicLevelRestriction d.ideal n ⋙
        finitePerfectAdicLocalRealization X d W := by
  have := (finitePerfectAdicConstant_exact X A).1
  have := (finitePerfectAdicConstant_exact X A).2.1
  have := (finitePerfectAdicConstant_exact X A).2.2
  have := (ringedOverFunctor_exactGeneral (completedAdicRing X d) W).1
  have := (ringedOverFunctor_exactGeneral (completedAdicRing X d) W).2.1
  have := (ringedOverFunctor_exactGeneral (completedAdicRing X d) W).2.2
  let R := ModuleCat.restrictScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let H := finitePerfectAdicScalarModelOrdinary X d
  let O := SheafOfModules.overFunctor (completedAdicRing X d) W
  exact (mapDerivedCategoryCompIso R (H ⋙ O)).symm ≪≫
    isoWhiskerLeft R.mapDerivedCategory (mapDerivedCategoryCompIso H O).symm ≪≫
    isoWhiskerRight (isoWhiskerLeft R.mapDerivedCategory
      (finitePerfectAdicScalarModelCompletedFactors X d)) O.mapDerivedCategory

/-- The specified source compositor on derived constant complexes.
Source: Stacks Tags 03DA, 03CY and 06YY. -/
def finitePerfectAdicScalarModelSourceStep :
    DerivedCategory.adicStepRestriction d.ideal n ⋙
        finitePerfectAdicScalarModelSource X d V U W f (n + 1) ≅
      finitePerfectAdicScalarModelSource X d V U W f n := by
  let q := Ideal.Quotient.factorPowSucc d.ideal (n + 1)
  exact finitePerfectAdicPasteCoefficientStep
    (finitePerfectAdicAlgebraLiftRestrict q).symm
    (finitePerfectAdicPasteCoefficientStep
      (normalizationConstantRestrict V.left.smallEtaleTopology (RingHom.ulift q)).symm
      (finitePerfectAdicPasteCoefficientStep
        (localProEtaleComparisonCoefficients U.hom (RingHom.ulift q))
        (finitePerfectAdicScalarCoherence X d V U W f n)))

/-- Localization of the ordinary source square is its prescribed derived square.

Source: Stacks Project, Tags 05RU and 06YY, exact-functor localization; Tags 03DA and
03CY for the ordinary coefficient comparisons.
(blueprint: lem-weil-pbc-finite-perfect-adic-scalar-model-localization).

Proof: expand the ordinary source compositor into coefficient lift, constants,
comparison inverse image, pro-etale inverse image, and associated scalar realization.
Each derived comparison in the specified source compositor is the localization of
that ordinary comparison. Apply functoriality of exact localization to the five
isomorphisms. Its composition and whiskering identities identify their pasted
localization with the left side. The four composition isomorphisms in SourceFactors
cancel the intermediate factorizations. Equivalently, precompose with Q and then
postcompose with the invertible exact-functor factorizations; the two maps reduce in
every degree to the same ordinary compositor. Localization detects their equality.
This is an identity of functors independent of any tower, perfectness, completed
coefficient comparison, or supplied natural isomorphism between source and target. -/
theorem finitePerfectAdicScalarModelSource_localization :
    let Q := ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    (mapDerivedCategoryCompIso Q
        (finitePerfectAdicOrdinaryScalarSource X d V U W f (n + 1))).inv ≫
      whiskerLeft Q.mapDerivedCategory
        (finitePerfectAdicScalarModelSourceFactors X d V U W f (n + 1)).hom ≫
      (finitePerfectAdicScalarModelSourceStep X d V U W f n).hom =
    (mapDerivedCategoryNatIso
      (finitePerfectAdicOrdinaryScalarSourceStep X d V U W f n)).hom ≫
      (finitePerfectAdicScalarModelSourceFactors X d V U W f n).hom  := by
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology V.left) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).1
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).2.1
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).2.2
  have := (finitePerfectAdicScalarModules_exact X d V U W f (n + 1)).1
  have := (finitePerfectAdicScalarModules_exact X d V U W f (n + 1)).2.1
  have := (finitePerfectAdicScalarModules_exact X d V U W f (n + 1)).2.2
  let B := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))
  let D := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
  let q : B →+* D := RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
  let LB := finitePerfectAdicScalarModelLift (A ⧸ d.ideal ^ (n + 1 + 1))
  let LD := finitePerfectAdicScalarModelLift (A ⧸ d.ideal ^ (n + 1))
  let CB := constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} B)
  let CD := constantSheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} D)
  let PB := ProEtale.comparisonUpperStar (ModuleCat.{t + 1} B) V.left
  let PD := ProEtale.comparisonUpperStar (ModuleCat.{t + 1} D) V.left
  let UB := ProEtale.upperStar (ModuleCat.{t + 1} B) U.hom
  let UD := ProEtale.upperStar (ModuleCat.{t + 1} D) U.hom
  let SB := finitePerfectAdicScalarModules X d V U W f (n + 1)
  let SD := finitePerfectAdicScalarModules X d V U W f n
  let eU : sheafCompose (ProEt.topology V.left) (ModuleCat.restrictScalars.{t + 1} q) ⋙
      UB ≅ UD ⋙ sheafCompose (ProEt.topology U.left)
        (ModuleCat.restrictScalars.{t + 1} q) :=
    normalizationPullbackIso (ProEt.topology V.left)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom) (ProEt.topology U.left) q
  let eP : sheafCompose V.left.smallEtaleTopology (ModuleCat.restrictScalars.{t + 1} q) ⋙
      PB ≅ PD ⋙ sheafCompose (ProEt.topology V.left)
        (ModuleCat.restrictScalars.{t + 1} q) :=
    normalizationPullbackIso V.left.smallEtaleTopology (toProEt V.left)
      (ProEt.topology V.left) q
  let eC := (constantCommuteCompose V.left.smallEtaleTopology
    (ModuleCat.restrictScalars.{t + 1} q)).symm
  let eL := finitePerfectAdicScalarModelLiftStep d n
  let zS := finitePerfectAdicScalarModulesCoherence X d V U W f n
  let wS := finitePerfectAdicScalarCoherence X d V U W f n
  have hS : (mapDerivedCategoryCompIso
      (sheafCompose (ProEt.topology U.left) (ModuleCat.restrictScalars.{t + 1} q)) SB).inv ≫
      whiskerLeft _ (Iso.refl SB.mapDerivedCategory).hom ≫ wS.hom =
      (mapDerivedCategoryNatIso zS).hom ≫ (Iso.refl SD.mapDerivedCategory).hom := by
    apply NatTrans.ext
    funext M
    simp only [q, SB, SD, zS, wS, finitePerfectAdicScalarCoherence, Iso.trans_hom,
      Iso.refl_hom, NatTrans.comp_app, whiskerLeft_app, NatTrans.id_app,
      Functor.comp_obj, Category.comp_id]
    erw [Category.id_comp, Iso.inv_hom_id_app_assoc]
  let zU := finitePerfectAdicPasteCoefficientStep eU zS
  let wU := finitePerfectAdicPasteCoefficientStep (mapDerivedCategorySquareIso eU) wS
  let aU := finitePerfectAdicDerivedFactor UB SB (Iso.refl SB.mapDerivedCategory)
  let bU := finitePerfectAdicDerivedFactor UD SD (Iso.refl SD.mapDerivedCategory)
  have hU := localizedPaste eU zS (Iso.refl SB.mapDerivedCategory)
    (Iso.refl SD.mapDerivedCategory) wS hS
  let zP := finitePerfectAdicPasteCoefficientStep eP zU
  let wP := finitePerfectAdicPasteCoefficientStep (mapDerivedCategorySquareIso eP) wU
  let aP := finitePerfectAdicDerivedFactor PB (UB ⋙ SB) aU
  let bP := finitePerfectAdicDerivedFactor PD (UD ⋙ SD) bU
  have hP := localizedPaste eP zU aU bU wU hU
  let zC := finitePerfectAdicPasteCoefficientStep eC zP
  let wC := finitePerfectAdicPasteCoefficientStep (mapDerivedCategorySquareIso eC) wP
  let aC := finitePerfectAdicDerivedFactor CB (PB ⋙ UB ⋙ SB) aP
  let bC := finitePerfectAdicDerivedFactor CD (PD ⋙ UD ⋙ SD) bP
  have hC := localizedPaste eC zP aP bP wP hP
  have hL := localizedPaste eL zC aC bC wC hC
  have hLE : mapDerivedCategorySquareIso eL =
      (finitePerfectAdicAlgebraLiftRestrict
        (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).symm := rfl
  have hCE : mapDerivedCategorySquareIso eC =
      (normalizationConstantRestrict V.left.smallEtaleTopology q).symm :=
    squareSymm _
  have hPU : finitePerfectAdicPasteCoefficientStep
      (mapDerivedCategorySquareIso eP) (mapDerivedCategorySquareIso eU) =
        localProEtaleComparisonCoefficients U.hom q :=
    (pasteAssociators _ _).symm
  have hWL : finitePerfectAdicPasteCoefficientStep
      (mapDerivedCategorySquareIso eL) wC =
        finitePerfectAdicScalarModelSourceStep X d V U W f n := by
    dsimp only [wC, wP, wU]
    rw [pasteAssoc (mapDerivedCategorySquareIso eP) (mapDerivedCategorySquareIso eU) wS,
      hPU, hCE, hLE]
    rfl
  let Q := ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
  let aL := finitePerfectAdicDerivedFactor LB (CB ⋙ PB ⋙ UB ⋙ SB) aC
  have hw := congrArg
    (fun z ↦ (mapDerivedCategoryCompIso Q (LB ⋙ CB ⋙ PB ⋙ UB ⋙ SB)).inv ≫
      whiskerLeft Q.mapDerivedCategory aL.hom ≫ z) (congrArg Iso.hom hWL)
  exact hw.symm.trans hL

end AlgebraicGeometry.Scheme
