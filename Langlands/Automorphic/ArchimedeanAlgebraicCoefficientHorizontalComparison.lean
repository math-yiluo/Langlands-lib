import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientTensorComparison
import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticHorizontalFinite
import Langlands.Cohomology.Lie.HorizontalCohomologyEquivalence

/-! # Actual algebraic tensor cohomology and analytic comparison -/

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

local instance horizontalComparisonRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalComparisonContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalComparisonSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalComparisonFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalComparisonStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance horizontalComparisonSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- Original algebraic tensor covariance restricted to the actual reduced
Lie algebra. -/
theorem tensorAlgebraicCompactRepresentation_reduced_lie
    (k : standardInfiniteCompact F n) (X : ReducedComplexLieAlgebra F n)
    (v : S.Space ⊗[ℂ] Space e ρ) :
    S.tensorCompactRepresentation (compactRepresentation e ρ) k ⁅X, v⁆ =
      ⁅reducedCompactRepresentation F n k X,
        S.tensorCompactRepresentation (compactRepresentation e ρ) k v⁆ := by
  change S.tensorCompactRepresentation (compactRepresentation e ρ) k
      (S.tensorComplexLieAction (Space e ρ) (reducedComplexInclusion F n X) v) =
    S.tensorComplexLieAction (Space e ρ)
      (reducedComplexInclusion F n (reducedCompactRepresentation F n k X))
      (S.tensorCompactRepresentation (compactRepresentation e ρ) k v)
  have hk : reducedComplexInclusion F n (reducedCompactRepresentation F n k X) =
      complexLieConjugation F n k.val (reducedComplexInclusion F n X) :=
    reducedComplexInclusion_conjugation F n k.val X
  exact (tensorCompactRepresentation_lie e ρ S k (reducedComplexInclusion F n X) v).trans
    (congrArg (fun Z : ComplexLieAlgebra F n =>
      S.tensorComplexLieAction (Space e ρ) Z
        (S.tensorCompactRepresentation (compactRepresentation e ρ) k v)) hk).symm

/-- Original finite translation is a map for the original reduced algebraic
tensor Lie action. -/
def tensorAlgebraicFiniteReducedLieHom (d : FiniteAdelicGL F n) :
    (S.Space ⊗[ℂ] Space e ρ) →ₗ⁅ℂ, ReducedComplexLieAlgebra F n⁆
      (S.Space ⊗[ℂ] Space e ρ) where
  toLinearMap := S.tensorFiniteRepresentation (Space e ρ) d
  map_lie' := S.tensorFiniteRepresentation_reducedLieAction (Space e ρ) d _ _

variable [NeZero n]

/-- Proved analytic insertion and the actual full horizontal coefficient
equivalence imply insertion for the original algebraic coefficient action. -/
theorem tensorAlgebraicHorizontal_infinitesimal (q : ℕ)
    (f : (ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] (S.Space ⊗[ℂ] Space e ρ))
    (hf : f ∈ S.tensorHorizontalSubmodule (compactRepresentation e ρ) q)
    (Y : ReducedComplexLieAlgebra F n) (hY : Y ∈ compactInReducedSubmodule F n)
    (X : Fin q → ReducedComplexLieAlgebra F n) :
    ⁅Y, f X⁆ = ∑ j, f (Function.update X j ⁅Y, X j⁆) := by
  let a := tensorAnalyticAlgebraicHorizontalEquiv e ρ S q
  let g := a.symm ⟨f, hf⟩
  let E := tensorAnalyticAlgebraicReducedLieEquiv e ρ S
  have hg : ∀ xs : Fin q → ReducedComplexLieAlgebra F n, E (g.val xs) = f xs := by
    intro xs
    exact congrArg
      (fun h : S.tensorHorizontalSubmodule (compactRepresentation e ρ) q => h.val xs)
      (a.apply_symm_apply ⟨f, hf⟩)
  calc
    ⁅Y, f X⁆ = E ⁅Y, g.val X⁆ :=
      (congrArg (fun v : S.Space ⊗[ℂ] Space e ρ => ⁅Y, v⁆) (hg X).symm).trans
        (E.map_lie Y (g.val X)).symm
    _ = E (∑ j, g.val (Function.update X j ⁅Y, X j⁆)) :=
      congrArg E (tensorAnalyticHorizontal_infinitesimal e ρ S q g.val g.property Y hY X)
    _ = ∑ j, f (Function.update X j ⁅Y, X j⁆) := by
      exact (map_sum E.toLinearMap (fun j : Fin q =>
        g.val (Function.update X j ⁅Y, X j⁆)) Finset.univ).trans
          (Finset.sum_congr rfl (fun j _ => hg (Function.update X j ⁅Y, X j⁆)))

local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "τa" => S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)
local notation "τb" => S.tensorCompactRepresentation (compactRepresentation e ρ)
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
local notation "hτa" => tensorAnalyticCompactRepresentation_reduced_lie e ρ S
local notation "hτb" => tensorAlgebraicCompactRepresentation_reduced_lie e ρ S
local notation "hιa" => tensorAnalyticHorizontal_infinitesimal e ρ S
local notation "hιb" => tensorAlgebraicHorizontal_infinitesimal e ρ S
local notation "Aa" => S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ)
local notation "Ab" => S.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ)
local notation "hAa" => tensorAnalyticHorizontalDifferential_finite e ρ S

/-- Restriction of the original algebraic coefficient differential to the
original full compact horizontal tensor cochains. -/
def tensorAlgebraicHorizontalDifferential (q : ℕ) :
    S.tensorHorizontalSubmodule (compactRepresentation e ρ) q →ₗ[ℂ]
      S.tensorHorizontalSubmodule (compactRepresentation e ρ) (q + 1) :=
  horizontalEquivariantDifferential H σ τb hσ hτb q (hιb q)

@[simp]
theorem tensorAlgebraicHorizontalDifferential_val (q : ℕ)
    (f : S.tensorHorizontalSubmodule (compactRepresentation e ρ) q) :
    (tensorAlgebraicHorizontalDifferential e ρ S q f).val =
      Langlands.Cohomology.Lie.differential q f.val := rfl

@[simp]
theorem tensorAlgebraicHorizontalDifferential_square (q : ℕ)
    (f : S.tensorHorizontalSubmodule (compactRepresentation e ρ) q) :
    tensorAlgebraicHorizontalDifferential e ρ S (q + 1)
      (tensorAlgebraicHorizontalDifferential e ρ S q f) = 0 :=
  Horizontal.differential_differential H σ τb hσ hτb hιb q f

/-- Original algebraic finite translation commutes with the actual horizontal
differential by the actual reduced coefficient Lie map. -/
theorem tensorAlgebraicHorizontalDifferential_finite (q : ℕ) (d : FiniteAdelicGL F n)
    (f : S.tensorHorizontalSubmodule (compactRepresentation e ρ) q) :
    tensorAlgebraicHorizontalDifferential e ρ S q (Ab q d f) =
      Ab (q + 1) d (tensorAlgebraicHorizontalDifferential e ρ S q f) := by
  apply Subtype.ext
  exact (Langlands.Cohomology.Lie.map_differential
    (tensorAlgebraicFiniteReducedLieHom e ρ S d) q f.val).symm

local notation "hAb" => tensorAlgebraicHorizontalDifferential_finite e ρ S

/-- Actual kernels for the original algebraic horizontal differential. -/
abbrev tensorAlgebraicHorizontalCycles (q : ℕ) :=
  Horizontal.cycles H σ τb hσ hτb hιb q

/-- Actual preceding algebraic differential ranges, zero in degree zero. -/
abbrev tensorAlgebraicHorizontalBoundaries (q : ℕ) :=
  Horizontal.boundaries H σ τb hσ hτb hιb q

abbrev tensorAlgebraicHorizontalBoundariesInCycles (q : ℕ) :=
  Horizontal.boundariesInCycles H σ τb hσ hτb hιb q

/-- The actual cycle quotient for the original algebraic coefficient action. -/
abbrev TensorAlgebraicHorizontalCohomology (q : ℕ) :=
  Horizontal.HorizontalCohomology H σ τb hσ hτb hιb q

abbrev tensorAlgebraicHorizontalClass (q : ℕ) :=
  Horizontal.cohomologyClass H σ τb hσ hτb hιb q

abbrev tensorAlgebraicHorizontalClass_surjective (q : ℕ) :=
  Horizontal.cohomologyClass_surjective H σ τb hσ hτb hιb q

abbrev tensorAlgebraicHorizontalClass_eq_zero {q : ℕ}
    (f : tensorAlgebraicHorizontalCycles e ρ S q) :=
  Horizontal.cohomologyClass_eq_zero H σ τb hσ hτb hιb f

abbrev tensorAlgebraicHorizontalCyclesFiniteRepresentation (q : ℕ) :=
  Horizontal.cyclesRepresentation H σ τb hσ hτb hιb Ab hAb q

abbrev tensorAlgebraicHorizontalCohomologyFiniteRepresentation (q : ℕ) :=
  Horizontal.cohomologyRepresentation H σ τb hσ hτb hιb Ab hAb q

abbrev tensorAlgebraicHorizontalCohomologyFiniteRepresentation_class (q : ℕ)
    (d : FiniteAdelicGL F n) (f : tensorAlgebraicHorizontalCycles e ρ S q) :=
  Horizontal.cohomologyRepresentation_class H σ τb hσ hτb hιb Ab hAb q d f

abbrev tensorAlgebraicHorizontalClassFiniteIntertwiner (q : ℕ) :=
  Horizontal.cohomologyClassIntertwiner H σ τb hσ hτb hιb Ab hAb q

/-- The actual horizontal coefficient equivalence is a chain equivalence for
the original analytic and algebraic restricted differentials. -/
theorem tensorAnalyticAlgebraicHorizontalDifferential (q : ℕ)
    (f : S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :
    tensorAlgebraicHorizontalDifferential e ρ S q
        (tensorAnalyticAlgebraicHorizontalEquiv e ρ S q f) =
      tensorAnalyticAlgebraicHorizontalEquiv e ρ S (q + 1)
        (tensorAnalyticHorizontalDifferential e ρ S q f) := by
  apply Subtype.ext
  exact (tensorAnalyticAlgebraicCochain_differential e ρ S q f.val).symm

local notation "a" => tensorAnalyticAlgebraicHorizontalEquiv e ρ S
local notation "ha" => tensorAnalyticAlgebraicHorizontalDifferential e ρ S

/-- The original coefficient comparison restricts to actual cycle
representations and retains original finite adelic translation. -/
abbrev tensorAnalyticAlgebraicHorizontalCyclesEquiv (q : ℕ) :=
  Horizontal.equivCycles H σ τa τb hσ hτa hτb hιa hιb Aa Ab hAa hAb a ha q

abbrev tensorAnalyticAlgebraicHorizontalCyclesEquiv_val (q : ℕ)
    (f : tensorAnalyticHorizontalCycles e ρ S q) :=
  Horizontal.equivCycles_val H σ τa τb hσ hτa hτb hιa hιb Aa Ab hAa hAb a ha q f

/-- Actual analytic and algebraic tensor horizontal cohomology representations
are equivalent by descent of the original coefficient chain equivalence. -/
abbrev tensorAnalyticAlgebraicHorizontalCohomologyEquiv (q : ℕ) :=
  Horizontal.equivCohomology H σ τa τb hσ hτa hτb hιa hιb Aa Ab hAa hAb a ha q

abbrev tensorAnalyticAlgebraicHorizontalCohomologyEquiv_class (q : ℕ)
    (f : tensorAnalyticHorizontalCycles e ρ S q) :=
  Horizontal.equivCohomology_class H σ τa τb hσ hτa hτb hιa hιb Aa Ab hAa hAb a ha q f

abbrev tensorAnalyticAlgebraicHorizontalCohomologyEquiv_symm_class (q : ℕ)
    (f : tensorAlgebraicHorizontalCycles e ρ S q) :=
  Horizontal.equivCohomology_symm_class H σ τa τb hσ hτa hτb hιa hιb Aa Ab hAa hAb a ha q f

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
