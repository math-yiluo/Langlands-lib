/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdPullbackComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization

/-! # Whole-tower pullback comparison data

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence
(blueprint: def-fd-pullback-comparison-datum).

The data use the recorded raw categories and operations. No completion of their
object sets and no arbitrary replacement comparison is introduced.

## Main definitions

* `FdPullbackSystem`: compatible finite and common-stage pullback comparisons.
* `FdCoefficientComparisonSystem`: simultaneous coefficient and realization data.
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

/-- The simultaneous finite-stage and common-stage pullback comparison. The compatible
transformation field is precisely the mixed scalar square, so it includes arbitrary
common stages, repeated stages and the actual beta maps of completed pullback.
Source: trace-definition final sentence, proof steps 8--9
(blueprint: def-fd-pullback-comparison-datum). -/
structure FdPullbackSystem {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (CU : FdCoefficientComparison l Ω U) (CT : FdCoefficientComparison l Ω T)
    (h : U ≅ T) where
  finite : ∀ E, FdPullbackComparison l Ω CU CT h E
  sfFamily : StageSystem.Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω U)
  sfFinite : ∀ E, HEq (sfFamily.Φ E)
    (rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) h.hom)
  sfBeta : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (e : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq ((sfFamily.β e).hom.app K)
      (commonStagePullbackComparison l Ω h.hom ⟨E, K⟩ L e).hom
  sfPair : sfFamily.functor = commonStageDerivedPullback l Ω h.hom
  mixed : StageSystem.Morphism.Hom
    (CT.family.comp (pbcQbarPullFamily l Ω h.hom)) (sfFamily.comp CU.family)
  mixed_components : ∀ E, HEq (mixed.τ E) (finite E).rational.hom
  pair : CT.equivalence.functor ⋙ pbcQbarCompletedPull l Ω h.hom ≅
    commonStageDerivedPullback l Ω h.hom ⋙ CU.equivalence.functor
  pair_components : ∀ P
    (K : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω P.stage) T),
    HEq P.obj K → HEq (pair.hom.app P)
      (((pbcScalarSystem l Ω U Fact.out Fact.out).ι P.stage).map
        ((finite P.stage).rational.hom.app K))

/-- The coefficient and scheme comparisons are simultaneous over every allowed scheme.
The realization data retain all the normalized whole-diagram composition/scalar equations.
Source: trace-definition final sentence, proof steps 1--9
(blueprint: def-fd-pullback-comparison-datum). -/
structure FdCoefficientComparisonSystem where
  realization : IntegralComparisonSystem.{u} l
  realization_coherent : ∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L),
    IntegralComparisonRealizationCoherence l
      (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω h) realization
  coefficients : ∀ (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))],
    FdCoefficientComparison l Ω T
  pullback : ∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ≅ T), FdPullbackSystem l Ω (coefficients U) (coefficients T) h

end WeilConjectures
