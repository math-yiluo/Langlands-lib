import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticModule
import Langlands.Global.ArchimedeanFiniteVectorCovariance

/-! # Actual orbit equivariance and analytic coefficient covariance -/

noncomputable section

universe uF

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ArchimedeanAlgebraicCoefficient

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GroupScheme
open scoped TensorProduct

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {I : Type} [Fintype I] (e : I → EmbeddingIndex F)
variable {m : Type} [Fintype m] [DecidableEq m]
variable (ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
    (CommRingCat.of ℂ)) m)

/-- The actual full orbit construction is equivariant for the original
point representation and right translation on genuine smooth functions. -/
def analyticOrbitIntertwiner :
    (analyticRepresentation e ρ).IntertwiningMap
      (vectorSmoothRightAction F n (m → ℂ)) where
  toLinearMap := (smoothOrbitMap e ρ).toLinearMap.comp (analyticCoordinates e ρ).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    change representation e ρ x (representation e ρ g v) =
      representation e ρ (x * g) v
    rw [map_mul]
    rfl

@[simp]
theorem analyticOrbitIntertwiner_apply (v : AnalyticSpace e ρ) :
    analyticOrbitIntertwiner e ρ v = smoothOrbitMap e ρ (analyticCoordinates e ρ v) := rfl

theorem analyticOrbitIntertwiner_injective :
    Function.Injective (analyticOrbitIntertwiner e ρ) :=
  (smoothOrbitMap_injective e ρ).comp (analyticCoordinates e ρ).injective

@[simp]
theorem analyticOrbitIntertwiner_rightAction (g : InfiniteAdelicGL F n)
    (v : AnalyticSpace e ρ) :
    analyticOrbitIntertwiner e ρ (analyticRepresentation e ρ g v) =
      vectorSmoothRightAction F n (m → ℂ) g (analyticOrbitIntertwiner e ρ v) :=
  Representation.IntertwiningMap.isIntertwining _ _ (analyticOrbitIntertwiner e ρ) g v

/-- The same actual orbit embedding intertwines the constructed analytic
Lie action on the entire coefficient carrier. -/
theorem analyticOrbitIntertwiner_lie (Z : ComplexLieAlgebra F n) (v : AnalyticSpace e ρ) :
    analyticOrbitIntertwiner e ρ ⁅Z, v⁆ =
      finiteVectorSmoothLieAction F n m Z (analyticOrbitIntertwiner e ρ v) :=
  smoothOrbitMap_analyticComplexDifferential e ρ Z (analyticCoordinates e ρ v)

/-- Full-group covariance of the genuine analytic coefficient action follows
from its injective equivariant orbit realization and actual function covariance. -/
theorem analyticRepresentation_lie (g : InfiniteAdelicGL F n)
    (Z : ComplexLieAlgebra F n) (v : AnalyticSpace e ρ) :
    analyticRepresentation e ρ g ⁅Z, v⁆ =
      ⁅complexLieConjugation F n g Z, analyticRepresentation e ρ g v⁆ := by
  apply analyticOrbitIntertwiner_injective e ρ
  rw [analyticOrbitIntertwiner_rightAction,
    analyticOrbitIntertwiner_lie,
    vectorSmoothRightAction_finiteVectorSmoothLieAction,
    analyticOrbitIntertwiner_lie,
    analyticOrbitIntertwiner_rightAction]

/-- The original full compact action on the analytically differentiated carrier. -/
def analyticCompactRepresentation :
    Representation ℂ (standardInfiniteCompact F n) (AnalyticSpace e ρ) :=
  (analyticRepresentation e ρ).comp (standardInfiniteCompact F n).subtype

omit [NumberField F] in
@[simp]
theorem analyticCompactRepresentation_apply (k : standardInfiniteCompact F n)
    (v : AnalyticSpace e ρ) :
    analyticCompactRepresentation e ρ k v = analyticRepresentation e ρ k.val v := rfl

theorem analyticCompactRepresentation_lie (k : standardInfiniteCompact F n)
    (Z : ComplexLieAlgebra F n) (v : AnalyticSpace e ρ) :
    analyticCompactRepresentation e ρ k ⁅Z, v⁆ =
      ⁅complexLieConjugation F n k.val Z, analyticCompactRepresentation e ρ k v⁆ :=
  analyticRepresentation_lie e ρ k.val Z v

section AutomorphicTensor

local instance analyticCovarianceRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance analyticCovarianceContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance analyticCovarianceSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance analyticCovarianceFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance analyticCovarianceStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance analyticCovarianceSpaceAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- Actual automorphic tensors with the constructed analytic coefficient action
have full-compact covariance without a supplied coefficient covariance premise. -/
theorem tensorAnalyticCompactRepresentation_lie (S : OperatorRealization F n)
    (k : standardInfiniteCompact F n) (Z : ComplexLieAlgebra F n)
    (t : S.Space ⊗[ℂ] AnalyticSpace e ρ) :
    S.tensorCompactRepresentation (analyticCompactRepresentation e ρ) k
        (S.tensorComplexLieAction (AnalyticSpace e ρ) Z t) =
      S.tensorComplexLieAction (AnalyticSpace e ρ) (complexLieConjugation F n k.val Z)
        (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ) k t) :=
  S.tensorCompactRepresentation_complexLieAction (AnalyticSpace e ρ)
    (analyticCompactRepresentation e ρ) (analyticCompactRepresentation_lie e ρ) k Z t

end AutomorphicTensor

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
