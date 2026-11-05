import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticHorizontal
import Langlands.Cohomology.Lie.HorizontalCohomologyAction

/-! # Finite adelic action on actual analytic coefficient tensor cohomology -/

noncomputable section

universe uF

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic.ArchimedeanAlgebraicCoefficient

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GroupScheme
open Langlands.Cohomology.Lie

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {I : Type} [Fintype I] (e : I → EmbeddingIndex F)
variable {m : Type} [Fintype m] [DecidableEq m]
variable (ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
    (CommRingCat.of ℂ)) m)

local instance analyticHorizontalFiniteRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance analyticHorizontalFiniteContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance analyticHorizontalFiniteSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance analyticHorizontalFiniteFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance analyticHorizontalFiniteStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance analyticHorizontalFiniteSpaceAddCommGroup :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- Original finite adelic translation is a map of the actual reduced diagonal
tensor Lie module. -/
def tensorAnalyticFiniteReducedLieHom (d : FiniteAdelicGL F n) :
    (S.Space ⊗[ℂ] AnalyticSpace e ρ) →ₗ⁅ℂ, ReducedComplexLieAlgebra F n⁆
      (S.Space ⊗[ℂ] AnalyticSpace e ρ) where
  toLinearMap := S.tensorFiniteRepresentation (AnalyticSpace e ρ) d
  map_lie' := S.tensorFiniteRepresentation_reducedLieAction (AnalyticSpace e ρ) d _ _

variable [NeZero n]

/-- The actual horizontal tensor differential commutes with original finite
adelic translation, by coefficient differential functoriality. -/
theorem tensorAnalyticHorizontalDifferential_finite (q : ℕ) (d : FiniteAdelicGL F n)
    (f : S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :
    tensorAnalyticHorizontalDifferential e ρ S q
        (S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ) q d f) =
      S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ) (q + 1) d
        (tensorAnalyticHorizontalDifferential e ρ S q f) := by
  apply Subtype.ext
  exact (Langlands.Cohomology.Lie.map_differential
    (tensorAnalyticFiniteReducedLieHom e ρ S d) q f.val).symm

/-- The genuine tensor horizontal differential as a finite adelic intertwiner. -/
def tensorAnalyticHorizontalDifferentialIntertwiner (q : ℕ) :
    (S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ) q).IntertwiningMap
      (S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ) (q + 1)) where
  toLinearMap := tensorAnalyticHorizontalDifferential e ρ S q
  isIntertwining' d := LinearMap.ext (tensorAnalyticHorizontalDifferential_finite e ρ S q d)

@[simp]
theorem tensorAnalyticHorizontalDifferentialIntertwiner_toLinearMap (q : ℕ) :
    (tensorAnalyticHorizontalDifferentialIntertwiner e ρ S q).toLinearMap =
      tensorAnalyticHorizontalDifferential e ρ S q := rfl

local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "τ" => S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
local notation "hτ" => tensorAnalyticCompactRepresentation_reduced_lie e ρ S
local notation "hι" => tensorAnalyticHorizontal_infinitesimal e ρ S
local notation "A" => S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ)
local notation "hA" => tensorAnalyticHorizontalDifferential_finite e ρ S

/-- Restrict original finite translation to actual closed tensor cochains. -/
abbrev tensorAnalyticHorizontalCyclesFiniteRepresentation (q : ℕ) :=
  Horizontal.cyclesRepresentation H σ τ hσ hτ hι A hA q

abbrev tensorAnalyticHorizontalCyclesFiniteRepresentation_val (q : ℕ)
    (d : FiniteAdelicGL F n) (f : tensorAnalyticHorizontalCycles e ρ S q) :=
  Horizontal.cyclesRepresentation_val H σ τ hσ hτ hι A hA q d f

/-- The induced actual finite adelic action on the existing tensor cohomology
quotient, using proved differential commutation. -/
abbrev tensorAnalyticHorizontalCohomologyFiniteRepresentation (q : ℕ) :=
  Horizontal.cohomologyRepresentation H σ τ hσ hτ hι A hA q

/-- A finite-translated class is represented by the original translated cycle. -/
abbrev tensorAnalyticHorizontalCohomologyFiniteRepresentation_class (q : ℕ)
    (d : FiniteAdelicGL F n) (f : tensorAnalyticHorizontalCycles e ρ S q) :=
  Horizontal.cohomologyRepresentation_class H σ τ hσ hτ hι A hA q d f

/-- The existing quotient projection intertwines original finite translation. -/
abbrev tensorAnalyticHorizontalClassFiniteIntertwiner (q : ℕ) :=
  Horizontal.cohomologyClassIntertwiner H σ τ hσ hτ hι A hA q

abbrev tensorAnalyticHorizontalClassFiniteIntertwiner_toLinearMap (q : ℕ) :=
  Horizontal.cohomologyClassIntertwiner_toLinearMap H σ τ hσ hτ hι A hA q

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
