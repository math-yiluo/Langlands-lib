/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory
public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Coherent coefficient comparison data

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence
(blueprint: def-fd-coefficient-comparison-datum).

The data use the recorded raw categories and operations. No completion of their
object sets and no arbitrary replacement comparison is introduced.

## Main definitions and statement

* `FdRationalStageComparison`: integral and raw rational stage comparisons.
* `FdOrdinaryScalarTransport`: generator-normalized ordinary scalar transport.
* `FdCoefficientComparison`: chi-normalized scalar and common-stage data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Avoid generating unused auxiliary lemmas for these large comparison structures.
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

open AlgebraicallyClosedCoefficients (Coefficient)

variable (l : ℕ) [Fact l.Prime]

/-- The actual scalar restriction through the quotient-normalized coefficient isomorphism.
Source: integral characterization, finite projections
(blueprint: def-fd-coefficient-comparison-datum). -/
def fdCoefficientTransport (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :=
  SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom

/-- Exactness uses the recorded ring isomorphism; this is its finite-limit adapter.
Source: integral characterization, scalar restriction
(blueprint: def-fd-coefficient-comparison-datum). -/
instance fdCoefficientTransportLimits (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    PreservesFiniteLimits (fdCoefficientTransport l E T) :=
  (integralDetailedCoefficientRestriction_exact T l E).1

/-- Exactness uses the same ring isomorphism; this is its finite-colimit adapter.
Source: integral characterization, scalar restriction
(blueprint: def-fd-coefficient-comparison-datum). -/
instance fdCoefficientTransportColimits (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    PreservesFiniteColimits (fdCoefficientTransport l E T) :=
  (integralDetailedCoefficientRestriction_exact T l E).2

/-- The named scalar restriction retains its existing additive structure.
Source: integral characterization, exact coefficient transport
(blueprint: def-fd-coefficient-comparison-datum). -/
instance fdCoefficientTransportAdditive (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    (fdCoefficientTransport l E T).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom).Additive

/-- The canonical exact localization comparison of the coefficient transport.
Source: integral characterization, derived transport
(blueprint: def-fd-coefficient-comparison-datum). -/
def fdCoefficientTransportFactors (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :=
  (fdCoefficientTransport l E T).mapDerivedCategoryFactors

/-- Pure tensors in the already defined raw localization, with its original module instances.
Source: trace-definition final sentence, localized Hom formula
(blueprint: def-fd-coefficient-comparison-datum). -/
def fdRawTensor {R : Type u} [CommRing R] {C : Type w} [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) {K H : C}
    (a : Localization.Away p) (f : K ⟶ H) :
    (ScalarLocalization.localization R C p).obj K ⟶
      (ScalarLocalization.localization R C p).obj H := a ⊗ₜ[R] f

/-- Scalar multiplication in the recorded raw localization, retaining its module instance.
Source: trace-definition final sentence, common-stage scalar formula
(blueprint: def-fd-coefficient-comparison-datum). -/
def fdRawScale {R : Type u} [CommRing R] {C : Type w} [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (a : Localization.Away p)
    {K H : ScalarLocalization R C p} (f : K ⟶ H) : K ⟶ H := a • f

variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Finite-stage comparison, including its identity on the common integral category and
on every localized pure tensor. Coefficient-size transport changes only the presentation.
Source: trace-definition final sentence, proof steps 1--2
(blueprint: def-fd-coefficient-comparison-datum). -/
structure FdRationalStageComparison (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (E : Padic.FiniteCoefficientFields l Ω) where
  integral : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T ≌
    pbcIntegralStage l Ω T E
  integral_identity : integral.functor ⋙ pbcStageInclusion l Ω T E =
    (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
      integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)
  [integral_shift : integral.functor.CommShift ℤ]
  integral_shift_normalization : ∀ (n : ℤ) K,
    HEq ((pbcStageInclusion l Ω T E).map
        ((integral.functor.commShiftIso n).hom.app K) ≫
      ((pbcStageInclusion l Ω T E).commShiftIso n).hom.app (integral.functor.obj K))
      ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).map
          (((sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι.commShiftIso n).hom.app K) ≫
        (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapDerivedCategory).commShiftIso
          n).hom.app K.obj)
  rational : sfRationalConstructibleCategory l
    (pbcFiniteField.{u} l Ω E) T ≌
    pbcStageCategory l Ω T E
  additive : rational.functor.Additive
  [shift : rational.functor.CommShift ℤ]
  exact : rational.functor.IsTriangulated
  inverse_exact : rational.inverse.CommShift ℤ
  inverse_triangles : (fun [_s : rational.inverse.CommShift ℤ] ↦
    rational.inverse.IsTriangulated) (_s := inverse_exact)
  objects : ∀ K, rational.functor.obj K = ⟨integral.functor.obj K.obj⟩
  shift_normalization : ∀ (n : ℤ) K,
    HEq (rational.functor.map
        (((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).commShiftIso
          n).hom.app K) ≫
      (rational.functor.commShiftIso n).hom.app
        ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K))
      ((pbcStageLocalization l Ω T E).map ((integral.functor.commShiftIso n).hom.app K) ≫
        ((pbcStageLocalization l Ω T E).commShiftIso n).hom.app (integral.functor.obj K))
  tensors : ∀ (K H : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l
      (pbcFiniteField.{u} l Ω E))) (f : K ⟶ H),
    HEq (rational.functor.map
      (fdRawTensor (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E)) a f))
      (fdRawTensor (pbcStageUniformizer.{u} l Ω E)
        ((pbcRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E)).symm
          (sfRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E) a))
        (integral.functor.map f))

attribute [instance] FdRationalStageComparison.shift FdRationalStageComparison.integral_shift

/-- Ordinary scalar transport fixed on all sheafified tensor generators. Its localization
will be composed with the specified quotient-map completion map, rather than an arbitrary iso.
Source: trace-definition final sentence, proof steps 3--4
(blueprint: def-fd-coefficient-comparison-datum). -/
structure FdOrdinaryScalarTransport (T : Scheme.{u})
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) where
  comparison :
    completedOrdinaryScalarExtension l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T ⋙
      fdCoefficientTransport l (pbcFiniteField.{u} l Ω L) T ≅
    fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T ⋙
      pbcExtend (pbcCompletedScalarMap l Ω T h)
  generators : ∀ (M : integralTowerModules l (pbcFiniteField.{u} l Ω E) T)
    (U : T.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l
      (pbcFiniteField.{u} l Ω L) T).obj.obj U) (x : M.val.obj U),
    (comparison.hom.app M).val.app U
      (completedScalarTensorSection l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T M U s x) =
      pbcTensorSection (pbcCompletedScalarMap l Ω T h)
        ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).obj M) U
        ((integralDetailedCoefficientComparison T l
          (pbcFiniteField.{u} l Ω L)).inv.hom.app U s) x

/-- The tensor-generator comparison on cochain complexes, retaining both composition factors.
Source: trace-definition final sentence, proof step 3
(blueprint: def-fd-coefficient-comparison-datum). -/
def FdOrdinaryScalarTransport.complex {T : Scheme.{u}}
    {E L : Padic.FiniteCoefficientFields l Ω} {h : E ≤ L}
    (m : FdOrdinaryScalarTransport l Ω T h) :=
  let F : integralTowerModules l (pbcFiniteField.{u} l Ω E) T ⥤
      integralTowerModules l (pbcFiniteField.{u} l Ω L) T :=
    completedOrdinaryScalarExtension l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T
  let G : integralTowerModules l (pbcFiniteField.{u} l Ω L) T ⥤
      pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω L)) :=
    fdCoefficientTransport l (pbcFiniteField.{u} l Ω L) T
  let H : integralTowerModules l (pbcFiniteField.{u} l Ω E) T ⥤
      pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)) :=
    fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T
  let J : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)) ⥤
      pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω L)) :=
    pbcExtend (pbcCompletedScalarMap l Ω T h)
  letI : F.Additive := completedOrdinaryScalarExtension_additive l
    (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T
  letI : G.Additive := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω L) T
  letI : H.Additive := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω E) T
  letI : J.Additive := pbcExtend_additive (pbcCompletedScalarMap l Ω T h)
  let c : F ⋙ G ≅ H ⋙ J := m.comparison
  Functor.mapHomologicalComplexCompIso
      (W₁ := integralTowerModules l (pbcFiniteField.{u} l Ω E) T)
      (W₂ := integralTowerModules l (pbcFiniteField.{u} l Ω L) T)
      (W₃ := pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω L)))
      (F := F) (G := G) (H := F ⋙ G) (Iso.refl _) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (W₁ := integralTowerModules l (pbcFiniteField.{u} l Ω E) T)
        (W₂ := pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)))
        (W₃ := pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω L)))
        (F := H) (G := J) (H := H ⋙ J) (Iso.refl _) (.up ℤ)).symm

/-- The actual scalar comparison chain map: coefficient transport followed by chi.
Its shifted-product coordinate is zero because chi is the specified quotient map.
Source: trace-definition final sentence, proof steps 3--4
(blueprint: def-fd-coefficient-comparison-datum). -/
def FdOrdinaryScalarTransport.completion {T : Scheme.{u}}
    {E L : Padic.FiniteCoefficientFields l Ω} {h : E ≤ L}
    (m : FdOrdinaryScalarTransport l Ω T h)
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) :=
  (m.complex l Ω).inv.app P ≫
    ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω L) T).mapHomologicalComplex
      (.up ℤ)).map ((completedScalarChainComparison l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).app P)

/-- One comparison of the raw systems, including the chi normalization, scalar cocycle,
shift compatibility, exact pair equivalence and common-stage scalar action.
Source: trace-definition final sentence, proof steps 1--6
(blueprint: def-fd-coefficient-comparison-datum). -/
structure FdCoefficientComparison (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] where
  stage : ∀ E, FdRationalStageComparison l Ω T E
  family : StageSystem.Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out)
  finite_functor : ∀ E, HEq (family.Φ E) (stage E).rational.functor
  [finite_shift : ∀ E, (family.Φ E).CommShift ℤ]
  finite_shift_normalization : ∀ E (n : ℤ),
    HEq ((family.Φ E).commShiftIso n) ((stage E).rational.functor.commShiftIso n)
  scalar_shift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    NatTrans.CommShift (family.β h).hom ℤ
  ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    FdOrdinaryScalarTransport l Ω T h
  integral_scalar : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
        integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
          pbcAmbientScalarExtension l Ω T h ≅
      sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T ⋙
        (sfIntegralConstructible l (pbcFiniteField.{u} l Ω L) T).ι ⋙
          integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)
  integral_scalar_lift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    ∃ c : (stage E).integral.functor ⋙
        pbcIntegralScalarExtension l Ω T dT.out iT.out h ≅
      sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T ⋙
        (stage L).integral.functor,
      (∀ K, HEq (c.hom.app K).hom ((integral_scalar h).hom.app K)) ∧
      (∀ K (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
        HEq ((family.β h).hom.app K')
        ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app
            ((stage E).integral.functor.obj K) ≫
          (pbcStageLocalization l Ω T L).map (c.hom.app K)))
  chi : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
      (DerivedCategory.Q.obj P.obj)),
    HEq ((integral_scalar h).hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
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
  equivalence : generalAlgebraicallyClosedConstructibleCategory l Ω T ≌
    pbcQbarCategory l Ω T
  pair_functor : equivalence.functor = family.functor
  [pair_shift : equivalence.functor.CommShift ℤ]
  pair_shift_finite : ∀ E (n : ℤ)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq ((equivalence.functor.commShiftIso n).hom.app ⟨E, K⟩)
      (((pbcScalarSystem l Ω T dT.out iT.out).ι E).map
          (((family.Φ E).commShiftIso n).hom.app K) ≫
        (((pbcScalarSystem l Ω T dT.out iT.out).ι E).commShiftIso n).hom.app
          ((family.Φ E).obj K))
  pair_exact : equivalence.functor.IsTriangulated
  pair_inverse_shift : equivalence.inverse.CommShift ℤ
  pair_inverse_exact : (fun [_s : equivalence.inverse.CommShift ℤ] ↦
    equivalence.inverse.IsTriangulated) (_s := pair_inverse_shift)
  pair_additive : equivalence.functor.Additive
  scalar : ∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T)
    (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (a : L.val) (f g : A.toStage hA ⟶ B.toStage hB)
    (K H : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω L) T)
    (f' : K ⟶ H), HEq K (A.toStage hA) → HEq H (B.toStage hB) → HEq f f' →
    HEq g (fdRawScale (C := sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω L) T)
      (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω L))
      ((sfRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω L)).symm
        ((Shrink.algEquiv ℚ_[l] L.val).symm a)) f') →
    equivalence.functor.map (StageSystem.PairCategory.mkHom L hA hB g) =
      (a : Ω) • equivalence.functor.map (StageSystem.PairCategory.mkHom L hA hB f)

attribute [instance] FdCoefficientComparison.finite_shift FdCoefficientComparison.pair_shift

end WeilConjectures
