import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientOrbitDifferential

/-! # The actual complexified analytic coefficient Lie module -/

noncomputable section

universe uF

open scoped Classical TensorProduct Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ArchimedeanAlgebraicCoefficient

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GroupScheme

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {I : Type} [Fintype I] (e : I → EmbeddingIndex F)
variable {m : Type} [Fintype m] [DecidableEq m]
variable (ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
    (CommRingCat.of ℂ)) m)

/-- Complex-linear extension of the constructed genuine real Frechet differential. -/
def analyticComplexDifferential :
    ComplexLieAlgebra F n →ₗ[ℂ] Module.End ℂ (Space e ρ) :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _ (analyticRealDifferential e ρ))

omit [NumberField F] in
@[simp]
theorem analyticComplexDifferential_tmul (z : ℂ) (X : RealLieAlgebra F n) :
    analyticComplexDifferential e ρ (z ⊗ₜ[ℝ] X) = z • analyticRealDifferential e ρ X := rfl

omit [DecidableEq m] in
private theorem finiteVectorSmoothLieAction_tmul (z : ℂ) (X : RealLieAlgebra F n) :
    finiteVectorSmoothLieAction F n m (z ⊗ₜ[ℝ] X) =
      z • finiteVectorSmoothDifferential F n m X := by
  have hz : z ⊗ₜ[ℝ] X = z • complexify F n X := by
    simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hz, map_smul]
  rfl

/-- The actual smooth orbit map intertwines the entire complexified analytic
Lie action, beyond the real directions alone. -/
theorem smoothOrbitMap_analyticComplexDifferential (Z : ComplexLieAlgebra F n) (v : Space e ρ) :
    smoothOrbitMap e ρ (analyticComplexDifferential e ρ Z v) =
      finiteVectorSmoothLieAction F n m Z (smoothOrbitMap e ρ v) := by
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
      rw [analyticComplexDifferential_tmul, finiteVectorSmoothLieAction_tmul]
      change smoothOrbitMap e ρ (z • analyticRealDifferential e ρ X v) = _
      rw [map_smul, smoothOrbitMap_analyticRealDifferential]
      rfl
  | add Z W hZ hW =>
      simp only [map_add, LinearMap.add_apply, hZ, hW]

/-- The complex Lie law follows from genuine orbit differentiation and
injectivity of the original full coefficient orbit map. -/
def analyticComplexLieAction :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (Space e ρ) :=
  { analyticComplexDifferential e ρ with
    map_lie' := by
      intro Z W
      apply LinearMap.ext
      intro v
      apply smoothOrbitMap_injective e ρ
      change smoothOrbitMap e ρ (analyticComplexDifferential e ρ ⁅Z, W⁆ v) =
        smoothOrbitMap e ρ (analyticComplexDifferential e ρ Z (analyticComplexDifferential e ρ W v) -
          analyticComplexDifferential e ρ W (analyticComplexDifferential e ρ Z v))
      simp only [map_sub, smoothOrbitMap_analyticComplexDifferential]
      exact congrArg (fun T : Module.End ℂ (VectorSmoothFunctions F n (m → ℂ)) =>
        T (smoothOrbitMap e ρ v)) ((finiteVectorSmoothLieAction F n m).map_lie Z W) }

@[simp]
theorem analyticComplexLieAction_tmul (z : ℂ) (X : RealLieAlgebra F n) :
    analyticComplexLieAction e ρ (z ⊗ₜ[ℝ] X) = z • analyticRealLieAction e ρ X := rfl

/-- The same full coordinate carrier, tagged by its genuinely differentiated
analytic Lie action, separately from the pre-existing algebraic action. -/
def AnalyticSpace := Space e ρ

instance : AddCommGroup (AnalyticSpace e ρ) := inferInstanceAs (AddCommGroup (Space e ρ))
instance : Module ℂ (AnalyticSpace e ρ) := inferInstanceAs (Module ℂ (Space e ρ))
instance : Module.Free ℂ (AnalyticSpace e ρ) := inferInstanceAs (Module.Free ℂ (Space e ρ))
instance : Module.Finite ℂ (AnalyticSpace e ρ) := inferInstanceAs (Module.Finite ℂ (Space e ρ))
instance : NormedAddCommGroup (AnalyticSpace e ρ) :=
  inferInstanceAs (NormedAddCommGroup (Space e ρ))
instance : NormedSpace ℂ (AnalyticSpace e ρ) := inferInstanceAs (NormedSpace ℂ (Space e ρ))
instance : CompleteSpace (AnalyticSpace e ρ) := inferInstanceAs (CompleteSpace (Space e ρ))

/-- All original vectors are retained. This equivalence makes no Lie-action comparison. -/
def analyticCoordinates : AnalyticSpace e ρ ≃ₗ[ℂ] Space e ρ := LinearEquiv.refl ℂ _

instance : LieRingModule (ComplexLieAlgebra F n) (AnalyticSpace e ρ) :=
  LieRingModule.compLieHom (L₂ := Module.End ℂ (AnalyticSpace e ρ))
    (AnalyticSpace e ρ) (analyticComplexLieAction e ρ)

instance : LieModule ℂ (ComplexLieAlgebra F n) (AnalyticSpace e ρ) where
  smul_lie z X v := by
    change analyticComplexLieAction e ρ (z • X) v = z • analyticComplexLieAction e ρ X v
    rw [map_smul]
    rfl
  lie_smul z X v := by
    change analyticComplexLieAction e ρ X (z • v) = z • analyticComplexLieAction e ρ X v
    exact map_smul (analyticComplexLieAction e ρ X) z v

@[simp]
theorem analyticCoordinates_lie (Z : ComplexLieAlgebra F n) (v : AnalyticSpace e ρ) :
    analyticCoordinates e ρ ⁅Z, v⁆ = analyticComplexLieAction e ρ Z (analyticCoordinates e ρ v) := rfl

/-- The original full point representation on the same analytic coefficient carrier. -/
def analyticRepresentation : Representation ℂ (InfiniteAdelicGL F n) (AnalyticSpace e ρ) :=
  representation e ρ

omit [NumberField F] in
@[simp]
theorem analyticCoordinates_representation (g : InfiniteAdelicGL F n) (v : AnalyticSpace e ρ) :
    analyticCoordinates e ρ (analyticRepresentation e ρ g v) =
      representation e ρ g (analyticCoordinates e ρ v) := rfl

/-- Restriction of the actual complex analytic action to the reduced Lie algebra. -/
def analyticReducedLieAction :
    ReducedComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (AnalyticSpace e ρ) :=
  (analyticComplexLieAction e ρ).comp (reducedComplexInclusion F n)

/-- Restriction of the same analytic action to the full complexified compact algebra. -/
def analyticCompactLieAction :
    CompactComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (AnalyticSpace e ρ) :=
  (analyticComplexLieAction e ρ).comp (compactComplexInclusion F n)

theorem analyticReducedLieAction_compact (X : CompactComplexLieAlgebra F n) :
    analyticReducedLieAction e ρ (compactToReducedComplex F n X) = analyticCompactLieAction e ρ X := by
  change analyticComplexLieAction e ρ
    (reducedComplexInclusion F n (compactToReducedComplex F n X)) = _
  rw [reducedComplexInclusion_compact]
  rfl

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
