import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticComparison
import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticHorizontal

/-! # Actual automorphic tensor comparison of analytic and algebraic coefficients -/

noncomputable section

universe uF

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic.ArchimedeanAlgebraicCoefficient

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GroupScheme

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {I : Type} [Fintype I] (e : I → EmbeddingIndex F)
variable {m : Type} [Fintype m] [DecidableEq m]
variable (ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
    (CommRingCat.of ℂ)) m)

local instance tensorComparisonRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorComparisonContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorComparisonSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorComparisonFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance tensorComparisonStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance tensorComparisonSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- Tensor the actual coefficient Lie equivalence with the identity on the
original automorphic realization. -/
def tensorAnalyticAlgebraicLieEquiv :
    (S.Space ⊗[ℂ] AnalyticSpace e ρ) ≃ₗ⁅ℂ, ComplexLieAlgebra F n⁆
      (S.Space ⊗[ℂ] Space e ρ) :=
  OperatorRealization.tensorComplexLieEquiv
    (Representation.Equiv.refl S.representation) (analyticAlgebraicLieEquiv e ρ)

@[simp]
theorem tensorAnalyticAlgebraicLieEquiv_tmul (f : S.Space) (v : AnalyticSpace e ρ) :
    tensorAnalyticAlgebraicLieEquiv e ρ S (f ⊗ₜ[ℂ] v) =
      f ⊗ₜ[ℂ] analyticCoordinates e ρ v := rfl

/-- The original full compact tensor actions are equivalent by the same
underlying coordinate tensor map. -/
def tensorAnalyticAlgebraicCompactEquiv :
    (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)).Equiv
      (S.tensorCompactRepresentation (compactRepresentation e ρ)) :=
  OperatorRealization.tensorCompactEquiv
    (Representation.Equiv.refl S.representation) (analyticAlgebraicCompactEquiv e ρ)

@[simp]
theorem tensorAnalyticAlgebraicCompactEquiv_apply (v : S.Space ⊗[ℂ] AnalyticSpace e ρ) :
    tensorAnalyticAlgebraicCompactEquiv e ρ S v =
      tensorAnalyticAlgebraicLieEquiv e ρ S v := rfl

theorem tensorAnalyticAlgebraicLieEquiv_finite (d : FiniteAdelicGL F n)
    (v : S.Space ⊗[ℂ] AnalyticSpace e ρ) :
    tensorAnalyticAlgebraicLieEquiv e ρ S
        (S.tensorFiniteRepresentation (AnalyticSpace e ρ) d v) =
      S.tensorFiniteRepresentation (Space e ρ) d (tensorAnalyticAlgebraicLieEquiv e ρ S v) :=
  OperatorRealization.tensorComplexLieEquiv_finite
    (Representation.Equiv.refl S.representation) (analyticAlgebraicLieEquiv e ρ) d v

/-- Restrict the original algebraic diagonal tensor action through the actual
reduced inclusion, independently of its analytic counterpart. -/
instance algebraicTensorReducedLieRingModule :
    LieRingModule (ReducedComplexLieAlgebra F n) (S.Space ⊗[ℂ] Space e ρ) :=
  LieRingModule.compLieHom (S.Space ⊗[ℂ] Space e ρ) (reducedComplexInclusion F n)

instance algebraicTensorReducedLieModule :
    LieModule ℂ (ReducedComplexLieAlgebra F n) (S.Space ⊗[ℂ] Space e ρ) :=
  LieModule.compLieHom (S.Space ⊗[ℂ] Space e ρ) (reducedComplexInclusion F n)

@[simp]
theorem tensorAlgebraicReduced_lie_eq (X : ReducedComplexLieAlgebra F n)
    (v : S.Space ⊗[ℂ] Space e ρ) :
    ⁅X, v⁆ = S.tensorReducedLieAction (Space e ρ) X v := rfl

/-- The reduced target uses the original algebraic coefficient operator on its
second tensor factor. -/
theorem tensorAlgebraicReduced_lie_tmul (X : ReducedComplexLieAlgebra F n)
    (f : S.Space) (v : Space e ρ) :
    ⁅X, f ⊗ₜ[ℂ] v⁆ =
      S.complexLieAction (reducedComplexInclusion F n X) f ⊗ₜ[ℂ] v +
        f ⊗ₜ[ℂ] lieAction e ρ (reducedComplexInclusion F n X) v :=
  S.tensorComplexLieAction_tmul (Space e ρ) (reducedComplexInclusion F n X) f v

/-- The same actual tensor comparison preserves the reduced Lie actions. -/
def tensorAnalyticAlgebraicReducedLieEquiv :
    (S.Space ⊗[ℂ] AnalyticSpace e ρ) ≃ₗ⁅ℂ, ReducedComplexLieAlgebra F n⁆
      (S.Space ⊗[ℂ] Space e ρ) :=
  { (tensorAnalyticAlgebraicLieEquiv e ρ S).toLinearEquiv with
    map_lie' := fun {X v} =>
      (tensorAnalyticAlgebraicLieEquiv e ρ S).map_lie (reducedComplexInclusion F n X) v }

@[simp]
theorem tensorAnalyticAlgebraicReducedLieEquiv_apply
    (v : S.Space ⊗[ℂ] AnalyticSpace e ρ) :
    tensorAnalyticAlgebraicReducedLieEquiv e ρ S v =
      tensorAnalyticAlgebraicLieEquiv e ρ S v := rfl

/-- Actual horizontal finite adelic representations are compared using the
original compact coefficient equivalence and unchanged automorphic vectors. -/
def tensorAnalyticAlgebraicHorizontalEquiv (q : ℕ) :
    (S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ) q).Equiv
      (S.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ) q) :=
  OperatorRealization.tensorHorizontalEquiv q
    (Representation.Equiv.refl S.representation) (analyticAlgebraicCompactEquiv e ρ)

@[simp]
theorem tensorAnalyticAlgebraicHorizontalEquiv_apply (q : ℕ)
    (f : S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q)
    (X : Fin q → ReducedComplexLieAlgebra F n) :
    (tensorAnalyticAlgebraicHorizontalEquiv e ρ S q f).val X =
      tensorAnalyticAlgebraicReducedLieEquiv e ρ S (f.val X) := rfl

/-- On all reduced cochains, the actual coefficient comparison commutes with
the original analytic and algebraic Chevalley–Eilenberg differentials. -/
theorem tensorAnalyticAlgebraicCochain_differential (q : ℕ)
    (f : (ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ]
      (S.Space ⊗[ℂ] AnalyticSpace e ρ)) :
    Langlands.Cohomology.Lie.map
        (tensorAnalyticAlgebraicReducedLieEquiv e ρ S).toLieModuleHom (q + 1)
        (Langlands.Cohomology.Lie.differential q f) =
      Langlands.Cohomology.Lie.differential q
        (Langlands.Cohomology.Lie.map
          (tensorAnalyticAlgebraicReducedLieEquiv e ρ S).toLieModuleHom q f) :=
  Langlands.Cohomology.Lie.map_differential
    (tensorAnalyticAlgebraicReducedLieEquiv e ρ S).toLieModuleHom q f

/-- The horizontal equivalence is postcomposition by that same actual
coefficient Lie equivalence. -/
theorem tensorAnalyticAlgebraicHorizontalEquiv_val (q : ℕ)
    (f : S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :
    (tensorAnalyticAlgebraicHorizontalEquiv e ρ S q f).val =
      Langlands.Cohomology.Lie.map
        (tensorAnalyticAlgebraicReducedLieEquiv e ρ S).toLieModuleHom q f.val := rfl

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
