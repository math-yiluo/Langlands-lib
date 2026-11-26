import Langlands.Global.AdelicNormOneCuspidalPairing
import Langlands.Global.AdelicMaximalUnipotentDecay

/-! # Norm-one approximation by classical cuspidal functions -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints RepresentationGrowth InfiniteAdelicGroupPoints

/-- Uniform moderate growth for the real directional derivative words used
in the adelic relative cuspidal decay estimate. -/
def HasUniformDirectionalHeightGrowth {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))
    (f : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ R : ℝ, 0 ≤ R ∧ ∀ s : List (smoothModel F d), ∃ C : ℝ, 0 ≤ C ∧
    ∀ x, ‖adelicIteratedDirectionalValue hsmooth s f x‖ ≤ C * adelicHeight F G rho x ^ R

/-- The norm-one restrictions of the specified classical cuspidal functions
of uniform moderate growth approximate each smooth cuspidal function of
uniform moderate growth in the quotient `L²` seminorm. -/
def AdelicNormOneClassicalCuspidalDensityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N)),
      IsCompact (Kinf : Set (InfiniteAdelicGroupPoints F G)) → 0 < N → IsClosedSubgroup rho →
    ∀ f : AdelicGroupPoints F G → ℂ,
      IsLeftInvariantUnder F G (rationalSubgroup F G) f → IsAdelicSmoothFunction F G f →
      HasZeroProperParabolicConstantTerms f → HasUniformDirectionalHeightGrowth hsmooth rho f →
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ ψ : AdelicGroupPoints F G → ℂ,
      IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
        (rationalSubgroup F G) Kinf rho ψ ∧ HasZeroProperParabolicConstantTerms ψ ∧
      HasUniformDirectionalHeightGrowth hsmooth rho ψ ∧
      eLpNorm (normOneRationalRestriction f - normOneRationalRestriction ψ) 2
        (normOneRationalQuotientHaarMeasure F G) < ε

end Langlands.Global
