/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
import WeilConjectures.FourierTransform.FdRawLocalization.FdRawLocalizationScalarCoherence
import WeilConjectures.FourierTransform.FdIntegralScalarDescentInputs
import WeilConjectures.FourierTransform.FdRawScalarComparisonPackaging

/-! # Coherence of the completion-inverse scalar comparisons

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final coefficient-category sentence; extracted comparison
argument, steps 3--4 (blueprint: lem-fd-completion-inverse-scalar-coherence).

The integral and rational identities are inputs. The conclusion retains the ordinary
transport, the quotient-normalized integral lift, and its rationalized inverse.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option linter.all false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.FdOrdinaryScalarTransport.complex
  WeilConjectures.FdOrdinaryScalarTransport.completion
  WeilConjectures.fdCoefficientTransportFactors
  AlgebraicGeometry.Scheme.pbcIntegralDatum
  AlgebraicGeometry.Scheme.completedAdicChangeData
  AlgebraicGeometry.Scheme.integralDetailedCoefficientComparison
universe d u w v u' v'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The inverse cocycle and both four-field contractions, written in the existing
stage-system language. This is a predicate on the specified comparisons, not new scalar data.
Source: trace-definition final sentence, comparison proof steps 5 and 8
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdInverseScalarCoherence
    {I : Type w} [Preorder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : I → Type u'} [∀ i, Category.{v'} (D i)]
    {S : StageSystem C} {P : StageSystem D} (F : S.Morphism P) : Prop :=
    (∀ {E L M : I}
    (h : E ≤ L) (k : L ≤ M)
    (K : C E),
    (F.β k).inv.app ((S.T h).obj K) ≫
      (P.T k).map ((F.β h).inv.app K) ≫
      (P.assoc h k).hom.app ((F.Φ E).obj K) =
    (F.Φ M).map
      ((S.assoc h k).hom.app K) ≫
      (F.β (h.trans k)).inv.app K) ∧
    (∀ {E L M N : I}
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N)
    (K : C E),
    ((F.β m).inv.app ((S.T k).obj
      ((S.T h).obj K)) ≫
      (P.T m).map
        ((F.β k).inv.app ((S.T h).obj K)) ≫
      (P.T m).map
        ((P.T k).map
        ((F.β h).inv.app K)) ≫
      (P.T m).map
        ((P.assoc h k).hom.app ((F.Φ E).obj K)) ≫
      (P.assoc (h.trans k) m).hom.app ((F.Φ E).obj K) =
      (F.Φ N).map
        ((S.T m).map
          ((S.assoc h k).hom.app K) ≫
          (S.assoc (h.trans k) m).hom.app K) ≫
      (F.β ((h.trans k).trans m)).inv.app K) ∧
    ((F.β m).inv.app ((S.T k).obj
      ((S.T h).obj K)) ≫
      (P.T m).map
        ((F.β k).inv.app ((S.T h).obj K)) ≫
      (P.T m).map
        ((P.T k).map
        ((F.β h).inv.app K)) ≫
      (P.assoc k m).hom.app
        ((P.T h).obj ((F.Φ E).obj K)) ≫
      (P.assoc h (k.trans m)).hom.app ((F.Φ E).obj K) =
      (F.Φ N).map
        ((S.T m).map
          ((S.assoc h k).hom.app K) ≫
          (S.assoc (h.trans k) m).hom.app K) ≫
      (F.β ((h.trans k).trans m)).inv.app K))

private theorem inverseScalarCocycle
    {I : Type w} [Preorder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : I → Type u'} [∀ i, Category.{v'} (D i)]
    {S : StageSystem C} {P : StageSystem D} (F : S.Morphism P)
    {E L M : I} (h : E ≤ L) (k : L ≤ M) (K : C E) :
    (F.β k).inv.app ((S.T h).obj K) ≫
      (P.T k).map ((F.β h).inv.app K) ≫
      (P.assoc h k).hom.app ((F.Φ E).obj K) =
    (F.Φ M).map ((S.assoc h k).hom.app K) ≫
      (F.β (h.trans k)).inv.app K := by
  apply (cancel_epi ((F.Φ M).map ((S.assoc h k).inv.app K))).mp
  have he := congrArg
    (fun f ↦ f ≫ (P.assoc h k).hom.app ((F.Φ E).obj K)) (F.coh_inv h k K)
  simp only [Category.assoc, Iso.inv_hom_id_app] at he
  erw [Category.comp_id] at he
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact he

private theorem inverseScalarCoherence
    {I : Type w} [Preorder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : I → Type u'} [∀ i, Category.{v'} (D i)]
    {S : StageSystem C} {P : StageSystem D} (F : S.Morphism P) :
    FdInverseScalarCoherence F := by
  refine ⟨inverseScalarCocycle F, ?_⟩
  intro E L M N h k m K
  have hleft :
      (F.β m).inv.app ((S.T k).obj ((S.T h).obj K)) ≫
        (P.T m).map ((F.β k).inv.app ((S.T h).obj K)) ≫
        (P.T m).map ((P.T k).map ((F.β h).inv.app K)) ≫
        (P.T m).map ((P.assoc h k).hom.app ((F.Φ E).obj K)) ≫
        (P.assoc (h.trans k) m).hom.app ((F.Φ E).obj K) =
      (F.Φ N).map ((S.T m).map ((S.assoc h k).hom.app K) ≫
        (S.assoc (h.trans k) m).hom.app K) ≫
        (F.β ((h.trans k).trans m)).inv.app K := by
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      Category.assoc, inverseScalarCocycle F h k K, Functor.map_comp, Category.assoc]
    have hn := (F.β m).inv.naturality ((S.assoc h k).hom.app K)
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    rw [inverseScalarCocycle F (h.trans k) m K, ← Functor.map_comp_assoc]
  refine ⟨hleft, ?_⟩
  rw [← P.cocycle h k m ((F.Φ E).obj K)]
  exact hleft

/-- The existing ordinary family, named to share its type across structure declarations.
Source: integral comparison data (blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionOrdinaryFamily
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
 :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h

/-- The existing comparison family, named to share its type across structure declarations.
Source: integral comparison data (blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionAmbientFamily
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
 :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
          integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
            pbcAmbientScalarExtension l Ω T h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T E L h ⋙
          (sfIntegralConstructible l (pbcFiniteField.{u} l Ω L) T).ι ⋙
            integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)

/-- The existing integral family, named to share its type across structure declarations.
Source: integral comparison data (blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionIntegralFamily
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (stage E).integral.functor ⋙ pbcIntegralScalarExtension l Ω T dT.out iT.out h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T E L h ⋙
          (stage L).integral.functor

/-- The existing quotient-cocone equation, named to keep generated structure recursors
from repeatedly expanding the derived coefficient presentations.
Source: the chi field below (blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionChi
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [_dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [_iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (ordinary : FdCompletionOrdinaryFamily l Ω T)
    (comparison : FdCompletionAmbientFamily l Ω T) : Prop :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
      (DerivedCategory.Q.obj P.obj)),
    HEq ((comparison h).hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
      (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
        ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
      (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
        ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj))
      ((pbcAmbientScalarExtension l Ω T h).map
        ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P.obj) ≫
      pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
        (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
          (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map ((ordinary h).completion l Ω P.obj))

attribute [local irreducible] FdCompletionChi

attribute [local irreducible] AlgebraicGeometry.Scheme.integralDetailedTransport

/-- The original ambient restriction equation.
Source: integral comparison data (blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionRestriction
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (comparison : FdCompletionAmbientFamily l Ω T)
    (integral : FdCompletionIntegralFamily l Ω T stage) : Prop :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      HEq ((integral h).hom.app K).hom ((comparison h).hom.app K)

attribute [local irreducible] FdCompletionRestriction FdCompletionOrdinaryFamily
  FdCompletionAmbientFamily FdCompletionIntegralFamily

/-- The quotient-normalized integral comparison retained by the scalar-coherence theorem.
This records exactly the tensor transport and chi lift of the coefficient datum, without
its downstream rational or pair-category conclusions.
Source: trace-definition final sentence, comparison steps 1--3
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
structure FdCompletionIntegralComparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) where
  ordinary : FdCompletionOrdinaryFamily l Ω T
  comparison : FdCompletionAmbientFamily l Ω T
  chi : FdCompletionChi l Ω T (@ordinary) (@comparison)
  integral : FdCompletionIntegralFamily l Ω T stage
  restriction : FdCompletionRestriction l Ω T stage comparison integral

attribute [local semireducible] FdCompletionOrdinaryFamily FdCompletionAmbientFamily
  FdCompletionIntegralFamily

/-- The existing finite_functor predicate, shared by the constructor and projections.
Source: the corresponding scalar-comparison field
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionFiniteFunctor
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out)) : Prop :=
  ∀ E, HEq (family.Φ E) (stage E).rational.functor

attribute [local irreducible] FdCompletionFiniteFunctor

/-- The existing finite_shift_normalization predicate, shared by the constructor and projections.
Source: the corresponding scalar-comparison field
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionShiftNormalization
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out))
    [s : ∀ E, (family.Φ E).CommShift ℤ] : Prop :=
  ∀ E (n : ℤ),
    HEq ((family.Φ E).commShiftIso n) ((stage E).rational.functor.commShiftIso n)

attribute [local irreducible] FdCompletionShiftNormalization

/-- The existing scalar_lift predicate, shared by the constructor and projections.
Source: the corresponding scalar-comparison field
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionScalarLift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (integral : FdCompletionIntegralComparison l Ω T stage)
    (family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out)) : Prop :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
    (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
    HEq ((family.β h).hom.app K')
      ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app
          ((stage E).integral.functor.obj K) ≫
        (pbcStageLocalization l Ω T L).map ((integral.integral h).hom.app K))

attribute [local irreducible] FdCompletionScalarLift

/-- The existing scalar_shift predicate, shared by the constructor and projections.
Source: the corresponding scalar-comparison field
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionScalarShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (_stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out))
    [s : ∀ E, (family.Φ E).CommShift ℤ] : Prop :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    NatTrans.CommShift (family.β h).hom ℤ ∧ NatTrans.CommShift (family.β h).inv ℤ

attribute [local irreducible] FdCompletionScalarShift

/-- The existing exact predicate, shared by the constructor and projections.
Source: the corresponding scalar-comparison field
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionExact
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (_stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out))
    [s : ∀ E, (family.Φ E).CommShift ℤ] : Prop :=
  ∀ E, (family.Φ E).IsTriangulated

attribute [local irreducible] FdCompletionExact

/-- The existing unit predicate, shared by the constructor and projections.
Source: the corresponding scalar-comparison field
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdCompletionUnit
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (_stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out)) : Prop :=
  ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq ((family.β (le_refl E)).inv.app K)
      ((family.Φ E).map
        ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω T E).hom.app K))

attribute [local irreducible] FdCompletionUnit

/-- Coherence data for the specified integral comparison and its rationalized inverse.
The stage-system components are identified with the supplied raw identity equivalences;
only presentation transport is expressed by heterogeneous equality.
Source: trace-definition final sentence, comparison steps 1--8
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
structure FdCompletionScalarComparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) where
  integral : FdCompletionIntegralComparison l Ω T stage
  family : StageSystem.Morphism
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
    (D := pbcStageCategory l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out)
  finite_functor : FdCompletionFiniteFunctor l Ω T stage family
  [finite_shift : ∀ E, (family.Φ E).CommShift ℤ]
  finite_shift_normalization : FdCompletionShiftNormalization l Ω T stage family
  scalar_lift : FdCompletionScalarLift l Ω T stage integral family
  scalar_shift : FdCompletionScalarShift l Ω T stage family
  exact : FdCompletionExact l Ω T stage family
  unit : FdCompletionUnit l Ω T stage family
  coherence : FdInverseScalarCoherence family

/-- The specified completion map restricts to an integral isomorphism, and its inverse
rationalizes to an exact scalar comparison satisfying shifts, units, the cocycle and
four-field compatibility, including repeated fields.
Source: blueprint main-20261015, trace-definition final sentence, expanded comparison
argument (blueprint: lem-fd-completion-inverse-scalar-coherence).

Proof, following the eight steps of the DAG node:
1. The stratified-perfect characterization identifies the integral categories after the
quotient-normalized coefficient transport. Finite-free scalar transport preserves them.
Completeness makes the specified ambient chi invertible, so it and its inverse restrict.
2. On a flat-term K-flat representative the ordinary transport fixes every tensor
factor. Chi has the actual quotient coordinates and zero shifted-product coordinate.
Quotient-scalar descent makes this normalization independent of the representative;
its countable-product exactness hypothesis holds on the small pro-etale site.
3. Ordinary derived tensor is exact. The cone shift comparison is (x,y) ↦ (x,(-1)^m y);
it fixes (c(z),0). Thus chi and its inverse commute with the specified shifts, and the
completed restriction is exact for those shifts and the inherited triangles.
4. The scalar-completion associator equation identifies the completed associator with
ordinary tensor balancing conjugated by these same chi maps. This is precisely the
normalization of the integral pullback realization and the chosen framework associator.
5. Naturality of chi moves its inner component across the outer scalar functor.
Multiplying by the inverse comparison on both sides and cancelling gives the inverse
cocycle with the stated arrow directions.
6. For equal fields ordinary multiplication identifies the tensor unit and chi is the
completeness unit. Its inverse is the normalized unit. The two associator unit equations
therefore give both comparison unit squares, also when all fields coincide.
7. Raw semilinear scalar localization sends these maps and their inverses to the
specified rational comparisons: the source uniformizer is invertible in the final
field. It preserves composition, whiskering, shifts and the integral-lift equation.
The identity raw equivalences preserve each scalar and integral tensor factor.
8. For four nested fields expand the three successive inverse comparisons. Twice use
the cocycle and naturality; the two contractions become j_30 followed by J_3 of the
two framework associator composites. The framework pentagon equates them, and the
PBC pentagon identifies the corresponding contractions on that side. Unit substitutions
cover every repeated-field degeneracy. -/
theorem fdCompletionInverseScalarCoherence
    (_D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ _D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) :
    Nonempty (FdCompletionScalarComparison l Ω T stage) := by
  classical
  obtain ⟨ordinary, comparison, b, hrestriction, hchi, hI, hshift, hexact,
    hlift, hcocycle, hunit⟩ := fdIntegralScalarDescentInputs _D l _hl Ω T stage
  obtain ⟨rawFamily, j, hjshift, hjlift, hjunit, hjcocycle, _, _, _⟩ :=
    FdRawLocalization.rawLocalizationScalarCoherence l Ω T stage _D _hl hI ordinary b
      hshift hexact hlift hcocycle hunit
  obtain ⟨F, s, hfinite, hnormalization, hscalarShift, hfiniteExact, hscalarUnit,
    hscalarLift⟩ := fdRawScalarComparisonPackaging l Ω T stage b rawFamily j
      hjshift hjlift hjunit hjcocycle
  let _ : ∀ E, (F.Φ E).CommShift ℤ := s
  let integral : FdCompletionIntegralComparison l Ω T stage := {
      ordinary := by unfold FdCompletionOrdinaryFamily; exact @ordinary
      comparison := by unfold FdCompletionAmbientFamily; exact @comparison
      chi := by
        unfold FdCompletionChi
        exact hchi
      integral := by unfold FdCompletionIntegralFamily; exact @b
      restriction := by unfold FdCompletionRestriction; exact hrestriction }
  exact ⟨{
    integral := integral
    family := F
    finite_functor := by unfold FdCompletionFiniteFunctor; exact hfinite
    finite_shift := s
    finite_shift_normalization := by unfold FdCompletionShiftNormalization; exact hnormalization
    scalar_lift := by unfold FdCompletionScalarLift; exact hscalarLift
    scalar_shift := by unfold FdCompletionScalarShift; exact hscalarShift
    exact := by unfold FdCompletionExact; exact hfiniteExact
    unit := by unfold FdCompletionUnit; exact hscalarUnit
    coherence := inverseScalarCoherence
      (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
      (D := pbcStageCategory l Ω T) F }⟩

end WeilConjectures
