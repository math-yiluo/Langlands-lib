/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback

/-! # Finite whole-tower pullback comparison data

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence
(blueprint: def-fd-finite-pullback-comparison-datum).

The data use the recorded raw categories and operations. No completion of their
object sets and no arbitrary replacement comparison is introduced.

## Main definitions

* `FdPullbackChain`: the normalized whole-tower comparison chain map.
* `FdPullbackComparison`: its integral and rational restrictions at one finite stage.
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

variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Stalk invertibility supplies the existing residue-field inverse required by the
framework operations. No extra scheme hypothesis is imposed.
Source: the coefficient convention in the trace definition
(blueprint: def-fd-finite-pullback-comparison-datum). -/
instance fdResidueInvertible (T : Scheme.{u})
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] (x : T) :
    Invertible (l : T.residueField x) :=
  (Eq.mp (congrArg IsUnit (map_natCast (T.residue x).hom l))
    ((iT.out x).map (T.residue x).hom)).invertible

/-- The actual strict pullback tower endomorphism, before realization.
Source: trace-definition final sentence, proof step 7
(blueprint: def-fd-finite-pullback-comparison-datum). -/
def fdPullbackEndomorphism (E : Padic.FiniteCoefficientFields l Ω)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((integralOperationsPullbackTowerFunctor l
      (pbcFiniteField.{u} l Ω E) h).obj P).obj (op n))
    (integralOperationsTowerStep
      ((integralOperationsPullbackTowerFunctor l (pbcFiniteField.{u} l Ω E) h).obj P))

/-- The canonical quotient projection from the whole strict pullback cone, in one degree.
Source: trace-definition final sentence, proof step 7
(blueprint: def-fd-finite-pullback-comparison-datum). -/
def fdPullbackProjection (E : Padic.FiniteCoefficientFields l Ω)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ)
    (i : ℤ) (n : ℕ) :=
  (CochainComplex.mappingCocone.fst (fdPullbackEndomorphism l Ω E h P)).f i ≫
    (Pi.π (fun n ↦ ((integralOperationsPullbackTowerFunctor l
      (pbcFiniteField.{u} l Ω E) h).obj P).obj (op n)) n).f i

/-- A whole-tower pullback comparison fixed by every quotient-unit component and zero
shifted component. In particular it cannot be inferred from equality of isolated reductions.
Source: trace-definition final sentence, proof steps 7--8
(blueprint: def-fd-finite-pullback-comparison-datum). -/
structure FdPullbackChain (E : Padic.FiniteCoefficientFields l Ω)
    {U T : Scheme.{u}} (h : U ⟶ T) where
  map :
    (fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex (.up ℤ) ⋙
        (pbcActualModulePull h (pbcStageDatum.{u} l Ω E)).mapHomologicalComplex (.up ℤ) ⟶
      integralOperationsPullbackComplexFunctor l (pbcFiniteField.{u} l Ω E) h ⋙
        (fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) U).mapHomologicalComplex (.up ℤ)
  quotients : ∀ (P : CochainComplex
      (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ)
    (i : ℤ) (n : ℕ) (V : T.ProEt) (x : (P.X i).val.obj (op V))
    (x' : ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).obj
      (P.X i)).val.obj (op V)), HEq x' x →
    HEq (((map.app P).f i ≫
        (fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) U).map
          (fdPullbackProjection l Ω E h P i n)).val.app
      (op ((proEtaleBaseChange h).obj V))
      (pbcActualModuleUnitSection h (pbcStageDatum.{u} l Ω E)
        ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).obj (P.X i)) V x'))
      (integralOperationsPullbackGenerator l (pbcFiniteField.{u} l Ω E) h n
        (((unrestrictedIntegralFiniteComplex l (pbcFiniteField.{u} l Ω E) T n).obj P).X i)
        V (coefficientIntegralScalarUnitSection l (pbcFiniteField.{u} l Ω E) T n
          (P.X i) (op V) x))
  shifted : ∀ (P : CochainComplex
      (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) (i : ℤ),
    (map.app P).f i ≫ (fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) U).map
      ((CochainComplex.mappingCocone.snd (fdPullbackEndomorphism l Ω E h P)).v
        i (i - 1) (by omega)) = 0

/-- The actual integral restriction of the completed pullback in the dependency.
Source: trace-definition final sentence, proof step 7
(blueprint: def-fd-finite-pullback-comparison-datum). -/
def fdPbcIntegralPull {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ⟶ T) (E : Padic.FiniteCoefficientFields l Ω) :
    pbcIntegralStage l Ω T E ⥤ pbcIntegralStage l Ω U E :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete U (pbcStageDatum.{u} l Ω E))
    (pbcStageInclusion l Ω T E ⋙ pbcActualCompletedPull h (pbcStageDatum.{u} l Ω E))
    (pbcQbarIntegralPull_mem l Ω h E)

/-- Pullback comparison on every integral and rational representative, before common-stage
passage. The ambient equation fixes its value by the whole quotient tower and its unit.
Source: trace-definition final sentence, proof steps 7--9
(blueprint: def-fd-finite-pullback-comparison-datum). -/
structure FdPullbackComparison {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (CU : FdCoefficientComparison l Ω U) (CT : FdCoefficientComparison l Ω T)
    (h : U ≅ T) (E : Padic.FiniteCoefficientFields l Ω) where
  chain : FdPullbackChain l Ω E h.hom
  integral : (CT.stage E).integral.functor ⋙ fdPbcIntegralPull l Ω h.hom E ≅
    constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h.hom ⋙
      (CU.stage E).integral.functor
  ambient : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
      integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
        pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω E) ≅
    constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h.hom ⋙
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) U).ι ⋙
        integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)
  lift : ∀ K, HEq (integral.hom.app K).hom (ambient.hom.app K)
  normalization : ∀ (P : (integralOperationsGoodComplex l
      (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
      (DerivedCategory.Q.obj P.obj)),
    HEq ((pbcActualCompletedPullUnit h.hom (pbcStageDatum.{u} l Ω E)).app
        ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj
          (DerivedCategory.Q.obj P.obj)) ≫
      ambient.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
      (integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)).map
        ((integralDerivedPullbackComparison l (pbcFiniteField.{u} l Ω E) h.hom).hom.app P) ≫
      (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) U).hom.app
        ((integralOperationsPullbackComplexFunctor l
          (pbcFiniteField.{u} l Ω E) h.hom).obj P.obj))
      ((pbcActualDerivedPull h.hom (pbcStageDatum.{u} l Ω E)).map
        ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P.obj) ≫
      pbcActualPullComplexCounit h.hom (pbcStageDatum.{u} l Ω E)
        (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
          (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map (chain.map.app P.obj))
  rational : (CT.stage E).rational.functor ⋙ (pbcQbarPullFamily l Ω h.hom).Φ E ≅
    rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) h.hom ⋙
      (CU.stage E).rational.functor
  rationalization : ∀ K,
    HEq (rational.hom.app
      ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K))
      ((pbcStageLocalization l Ω U E).map (integral.hom.app K))

end WeilConjectures
