import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticTensorCompact
import Langlands.Automorphic.ReducedCochainCompactDifferentiation
import Langlands.Cohomology.Lie.HorizontalCohomology

/-! # Actual relative cohomology of automorphic analytic coefficient tensors -/

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

local instance analyticHorizontalRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance analyticHorizontalContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance analyticHorizontalSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance analyticHorizontalFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance analyticHorizontalStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance analyticHorizontalSpaceAddCommGroup :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- Restrict the genuine full diagonal tensor action through the actual reduced
Lie algebra inclusion. -/
instance analyticTensorReducedLieRingModule :
    LieRingModule (ReducedComplexLieAlgebra F n) (S.Space ⊗[ℂ] AnalyticSpace e ρ) :=
  LieRingModule.compLieHom (S.Space ⊗[ℂ] AnalyticSpace e ρ) (reducedComplexInclusion F n)

instance analyticTensorReducedLieModule :
    LieModule ℂ (ReducedComplexLieAlgebra F n) (S.Space ⊗[ℂ] AnalyticSpace e ρ) :=
  LieModule.compLieHom (S.Space ⊗[ℂ] AnalyticSpace e ρ) (reducedComplexInclusion F n)

@[simp]
theorem tensorAnalyticReduced_lie_eq (X : ReducedComplexLieAlgebra F n)
    (v : S.Space ⊗[ℂ] AnalyticSpace e ρ) :
    ⁅X, v⁆ = S.tensorReducedLieAction (AnalyticSpace e ρ) X v := rfl

/-- The original full compact tensor action has covariance for the genuine
reduced action, with no coefficient compatibility premise. -/
theorem tensorAnalyticCompactRepresentation_reduced_lie
    (k : standardInfiniteCompact F n) (X : ReducedComplexLieAlgebra F n)
    (v : S.Space ⊗[ℂ] AnalyticSpace e ρ) :
    S.tensorCompactRepresentation (analyticCompactRepresentation e ρ) k ⁅X, v⁆ =
      ⁅reducedCompactRepresentation F n k X,
        S.tensorCompactRepresentation (analyticCompactRepresentation e ρ) k v⁆ := by
  change S.tensorCompactRepresentation (analyticCompactRepresentation e ρ) k
      (S.tensorComplexLieAction (AnalyticSpace e ρ) (reducedComplexInclusion F n X) v) =
    S.tensorComplexLieAction (AnalyticSpace e ρ)
      (reducedComplexInclusion F n (reducedCompactRepresentation F n k X))
      (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ) k v)
  have hk : reducedComplexInclusion F n (reducedCompactRepresentation F n k X) =
      complexLieConjugation F n k.val (reducedComplexInclusion F n X) :=
    reducedComplexInclusion_conjugation F n k.val X
  exact (tensorAnalyticCompactRepresentation_lie e ρ S k
    (reducedComplexInclusion F n X) v).trans
      (congrArg (fun Z : ComplexLieAlgebra F n =>
        S.tensorComplexLieAction (AnalyticSpace e ρ) Z
          (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ) k v)) hk).symm

variable [NeZero n]

/-- The actual reduced cochain extension transfers derived full-complex tensor
insertion to all reduced Lie tuples. -/
theorem tensorAnalyticReducedCochain_compact (q : ℕ)
    (f : (ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ]
      (S.Space ⊗[ℂ] AnalyticSpace e ρ))
    (hf : f ∈ HorizontalAlternating.equivariant (reducedCompactRepresentation F n)
      (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)) q)
    (Y : CompactComplexLieAlgebra F n) (X : Fin q → ReducedComplexLieAlgebra F n) :
    S.tensorCompactLieAction (AnalyticSpace e ρ) Y (f X) =
      ∑ j, f (Function.update X j ⁅compactToReducedComplex F n Y, X j⁆) := by
  have he := tensorAnalyticCochain_compact_complex e ρ S q
    (reducedCochainExtension F n q f)
    (reducedCochainExtension_equivariant F n
      (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)) q f hf)
    Y (fun j => reducedComplexInclusion F n (X j))
  have hvalue := congrArg (S.tensorCompactLieAction (AnalyticSpace e ρ) Y)
    (reducedCochainExtension_inclusion F n q f X).symm
  refine hvalue.trans (he.trans ?_)
  apply Finset.sum_congr rfl
  intro j _
  rw [reducedCochainExtension_apply]
  apply congrArg f
  funext k
  by_cases hk : k = j
  · subst k
    simp only [Function.update_self, (reducedComplexProjection F n).map_lie,
      reducedComplexProjection_compact, reducedComplexProjection_inclusion]
  · simp only [Function.update_of_ne hk, reducedComplexProjection_inclusion]

/-- Genuine full compact equivariance implies exactly the infinitesimal
identity needed for stability of horizontal tensor cochains. -/
theorem tensorAnalyticHorizontal_infinitesimal (q : ℕ)
    (f : (ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ]
      (S.Space ⊗[ℂ] AnalyticSpace e ρ))
    (hf : f ∈ S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q)
    (Y : ReducedComplexLieAlgebra F n) (hY : Y ∈ compactInReducedSubmodule F n)
    (X : Fin q → ReducedComplexLieAlgebra F n) :
    ⁅Y, f X⁆ = ∑ j, f (Function.update X j ⁅Y, X j⁆) := by
  obtain ⟨Z, rfl⟩ := hY
  change S.tensorComplexLieAction (AnalyticSpace e ρ)
    (reducedComplexInclusion F n (compactToReducedComplex F n Z)) (f X) = _
  rw [reducedComplexInclusion_compact]
  exact tensorAnalyticReducedCochain_compact e ρ S q f hf.2 Z X

local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "τ" => S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
local notation "hτ" => tensorAnalyticCompactRepresentation_reduced_lie e ρ S
local notation "hι" => tensorAnalyticHorizontal_infinitesimal e ρ S

/-- The actual coefficient differential on the original full-compact
horizontal automorphic tensors, with all stability premises derived. -/
def tensorAnalyticHorizontalDifferential (q : ℕ) :
    S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q →ₗ[ℂ]
      S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) (q + 1) :=
  horizontalEquivariantDifferential H σ τ hσ hτ q (hι q)

@[simp]
theorem tensorAnalyticHorizontalDifferential_val (q : ℕ)
    (f : S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :
    (tensorAnalyticHorizontalDifferential e ρ S q f).val =
      Langlands.Cohomology.Lie.differential q f.val := rfl

@[simp]
theorem tensorAnalyticHorizontalDifferential_square (q : ℕ)
    (f : S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :
    tensorAnalyticHorizontalDifferential e ρ S (q + 1)
      (tensorAnalyticHorizontalDifferential e ρ S q f) = 0 :=
  Horizontal.differential_differential H σ τ hσ hτ hι q f

/-- Closed cochains for the actual tensor horizontal differential. -/
abbrev tensorAnalyticHorizontalCycles (q : ℕ) :=
  Horizontal.cycles H σ τ hσ hτ hι q

/-- Actual differential images, with zero boundaries in degree zero. -/
abbrev tensorAnalyticHorizontalBoundaries (q : ℕ) :=
  Horizontal.boundaries H σ τ hσ hτ hι q

/-- The genuine boundary inclusion range inside the actual cycle module. -/
abbrev tensorAnalyticHorizontalBoundariesInCycles (q : ℕ) :=
  Horizontal.boundariesInCycles H σ τ hσ hτ hι q

/-- The actual quotient of closed full-compact horizontal tensor cochains by
the image of the genuine coefficient differential. -/
abbrev TensorAnalyticHorizontalCohomology (q : ℕ) :=
  Horizontal.HorizontalCohomology H σ τ hσ hτ hι q

/-- The actual cycle-to-cohomology quotient projection. -/
abbrev tensorAnalyticHorizontalClass (q : ℕ) :=
  Horizontal.cohomologyClass H σ τ hσ hτ hι q

abbrev tensorAnalyticHorizontalBoundaries_le_cycles (q : ℕ) :=
  Horizontal.boundaries_le_cycles H σ τ hσ hτ hι q

abbrev tensorAnalyticHorizontalClass_surjective (q : ℕ) :=
  Horizontal.cohomologyClass_surjective H σ τ hσ hτ hι q

abbrev tensorAnalyticHorizontalClass_eq_zero {q : ℕ}
    (f : tensorAnalyticHorizontalCycles e ρ S q) :=
  Horizontal.cohomologyClass_eq_zero H σ τ hσ hτ hι f

abbrev tensorAnalyticHorizontalClass_eq_iff {q : ℕ}
    (f g : tensorAnalyticHorizontalCycles e ρ S q) :=
  Horizontal.cohomologyClass_eq_iff H σ τ hσ hτ hι f g

abbrev tensorAnalyticHorizontalCoboundaryToCycles (q : ℕ) :=
  Horizontal.coboundaryToCycles H σ τ hσ hτ hι q

abbrev tensorAnalyticHorizontalClass_coboundary (q : ℕ)
    (f : S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :=
  Horizontal.cohomologyClass_coboundary H σ τ hσ hτ hι q f

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
