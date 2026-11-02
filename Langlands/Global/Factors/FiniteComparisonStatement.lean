import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Finite functional-equation comparison

A conditional engine for Henniart (1986), §4.3(2), (4), (5). Only the L tails
have infinite Euler products. Gamma products are always over a finite set.
The bare factor data carry no functional equation or existence assertion.
-/

noncomputable section

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

universe u

namespace Langlands.Global.FunctionalEquationComparison

/-- Equality of punctured germs at every complex point. Values assigned at
individual poles or removable singularities are immaterial. -/
def MeromorphicEq (f g : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, f =ᶠ[𝓝[≠] z] g

/-- A meromorphic function whose germ is nonzero at every point. A zero or pole
of finite order is allowed; an identically zero germ is excluded. -/
def NonzeroMeromorphic (f : ℂ → ℂ) : Prop :=
  Meromorphic f ∧ ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤

/-- Bare factors with a fixed dual, additive character, and Haar convention.
An application must supply the actual factors and their existence separately. -/
structure LocalFactors where
  lFactor : ℂ → ℂ
  dualLFactor : ℂ → ℂ
  epsilonFactor : ℂ → ℂ

/-- The convention is epsilon(s) L(dual,1-s) / L(s). -/
def LocalFactors.gamma (F : LocalFactors) (s : ℂ) : ℂ :=
  F.epsilonFactor s * F.dualLFactor (1 - s) / F.lFactor s

/-- Local factors at all places, and the two partial L-functions outside a
specified finite set. No analytic assertion is part of these data. -/
structure FiniteEulerData (Place : Type u) where
  localFactors : Place → LocalFactors
  partialL : ℂ → ℂ
  partialDualL : ℂ → ℂ

variable {Place : Type u}

/-- Finite completion of the partial L-function. -/
def FiniteEulerData.completedL (D : FiniteEulerData Place) (S : Finset Place)
    (s : ℂ) : ℂ :=
  D.partialL s * ∏ v ∈ S, (D.localFactors v).lFactor s

/-- Completion of the dual partial L-function, before reflection in s=1/2. -/
def FiniteEulerData.completedDualL (D : FiniteEulerData Place) (S : Finset Place)
    (s : ℂ) : ℂ :=
  D.partialDualL s * ∏ v ∈ S, (D.localFactors v).dualLFactor s

/-- All global epsilon contributions are placed in the same finite set S. -/
def FiniteEulerData.finiteEpsilon (D : FiniteEulerData Place) (S : Finset Place)
    (s : ℂ) : ℂ :=
  ∏ v ∈ S, (D.localFactors v).epsilonFactor s

/-- A finite gamma product; there is no Euler product of gamma factors. -/
def FiniteEulerData.finiteGamma (D : FiniteEulerData Place) (S : Finset Place)
    (s : ℂ) : ℂ :=
  ∏ v ∈ S, (D.localFactors v).gamma s

/-- Both partial L-functions are the actual outside-S Euler products on one
common right half-plane. This asserts existence of the product limits. -/
def HasEulerProductsOutside [DecidableEq Place] (D : FiniteEulerData Place)
    (S : Finset Place) (σ : ℝ) : Prop :=
  ∀ s : ℂ, σ < s.re →
    HasProd (fun v : {v : Place // v ∉ S} => (D.localFactors v).lFactor s)
      (D.partialL s) ∧
    HasProd (fun v : {v : Place // v ∉ S} => (D.localFactors v).dualLFactor s)
      (D.partialDualL s)

/-- Almost-everywhere local L matching: every place outside the same finite S,
for both the original and the dual factors on a common half-plane. -/
def MatchesOutside [DecidableEq Place] (D E : FiniteEulerData Place)
    (S : Finset Place) (σ : ℝ) : Prop :=
  ∀ v ∉ S, ∀ s : ℂ, σ < s.re →
    (D.localFactors v).lFactor s = (E.localFactors v).lFactor s ∧
    (D.localFactors v).dualLFactor s = (E.localFactors v).dualLFactor s

/-- Meromorphy and nonzero germs are hypotheses, including for each exceptional
local factor. Neither missing factors nor the zero function satisfy this input. -/
def Admissible (D : FiniteEulerData Place) (S : Finset Place) : Prop :=
  NonzeroMeromorphic D.partialL ∧ NonzeroMeromorphic D.partialDualL ∧
    ∀ v ∈ S, NonzeroMeromorphic (D.localFactors v).lFactor ∧
      NonzeroMeromorphic (D.localFactors v).dualLFactor ∧
      NonzeroMeromorphic (D.localFactors v).epsilonFactor

/-- The full completed functional equation, with every epsilon contribution
inside S. An adapter must justify this placement, including trivial epsilon
factors outside S; it is not inferred from L matching. -/
def FunctionalEquation (D : FiniteEulerData Place) (S : Finset Place) : Prop :=
  MeromorphicEq (D.completedL S)
    (fun s => D.finiteEpsilon S s * D.completedDualL S (1 - s))

/-- The explicit analytic and global inputs for one comparison. The common
half-plane can always be shrunk by increasing σ. -/
def ComparisonInputs [DecidableEq Place] (D E : FiniteEulerData Place)
    (S : Finset Place) : Prop :=
  Admissible D S ∧ Admissible E S ∧
    FunctionalEquation D S ∧ FunctionalEquation E S ∧
    ∃ σ : ℝ, HasEulerProductsOutside D S σ ∧ HasEulerProductsOutside E S σ ∧
      MatchesOutside D E S σ

/-- The identity theorem extends the equal outside-S Euler products. This target
uses only meromorphic continuation and product uniqueness, not a global FE. -/
def EulerTailComparisonStatement : Prop :=
  ∀ (Place : Type u) [DecidableEq Place] (S : Finset Place)
    (D E : FiniteEulerData Place) (σ : ℝ),
    Meromorphic D.partialL → Meromorphic D.partialDualL →
    Meromorphic E.partialL → Meromorphic E.partialDualL →
    HasEulerProductsOutside D S σ → HasEulerProductsOutside E S σ →
    MatchesOutside D E S σ →
    MeromorphicEq D.partialL E.partialL ∧
      MeromorphicEq D.partialDualL E.partialDualL

/-- Cancellation of two full FEs with matching partial L-functions. -/
def FiniteGammaComparisonStatement : Prop :=
  ∀ (Place : Type u) (S : Finset Place) (D E : FiniteEulerData Place),
    Admissible D S → Admissible E S →
    FunctionalEquation D S → FunctionalEquation E S →
    MeromorphicEq D.partialL E.partialL →
    MeromorphicEq D.partialDualL E.partialDualL →
    MeromorphicEq (D.finiteGamma S) (E.finiteGamma S)

/-- The finite product identity directly from almost-everywhere L matching and
the two completed functional equations; compare Henniart §4.3(2). -/
def GlobalFiniteGammaComparisonStatement : Prop :=
  ∀ (Place : Type u) [DecidableEq Place] (S : Finset Place)
    (D E : FiniteEulerData Place),
    ComparisonInputs D E S → MeromorphicEq (D.finiteGamma S) (E.finiteGamma S)

/-- Cancel every auxiliary factor outside an arbitrary retained block A.
The block may contain all archimedean places, whose individual factors need
not agree. Cancellation is only permitted for nonzero meromorphic germs. -/
def FiniteBlockCancellationStatement : Prop :=
  ∀ (Place : Type u) [DecidableEq Place] (S A : Finset Place)
    (F G : Place → ℂ → ℂ), A ⊆ S →
    (∀ v ∈ S, NonzeroMeromorphic (F v) ∧ NonzeroMeromorphic (G v)) →
    MeromorphicEq (fun s => ∏ v ∈ S, F v s) (fun s => ∏ v ∈ S, G v s) →
    (∀ v ∈ S, v ∉ A → MeromorphicEq (F v) (G v)) →
    MeromorphicEq (fun s => ∏ v ∈ A, F v s) (fun s => ∏ v ∈ A, G v s)

/-- Equality of the factors at all places where a twist is prescribed trivial.
This is an input to the generic engine, to be proved by the actual adapter. -/
def PreservesGamma (D : FiniteEulerData Place) (F : Place → LocalFactors)
    (A : Finset Place) : Prop :=
  ∀ v ∈ A, MeromorphicEq (D.localFactors v).gamma (F v).gamma

/-- A local gamma comparison at every specified auxiliary place. Actual uses
must supply highly ramified stability and its character/central-character
hypotheses individually; this predicate does not assert stability exists. -/
def StableGamma (D E : FiniteEulerData Place) (A : Finset Place) : Prop :=
  ∀ v ∈ A, MeromorphicEq (D.localFactors v).gamma (E.localFactors v).gamma

/-- First compare the whole archimedean product using a twist stable at every
finite member of S. Use a second twist preserving the chosen finite place w,
stable at every other finite member of S, to isolate w. A is the complete
archimedean set in an actual application, and S also contains all exceptional
places. No individual archimedean comparison is assumed or concluded. -/
def TwoTwistIsolationStatement : Prop :=
  ∀ (Place : Type u) [DecidableEq Place] (S A : Finset Place) (w : Place)
    (F G : Place → LocalFactors)
    (D₁ E₁ D₂ E₂ : FiniteEulerData Place),
    A ⊆ S → w ∈ S → w ∉ A →
    ComparisonInputs D₁ E₁ S → ComparisonInputs D₂ E₂ S →
    PreservesGamma D₁ F A → PreservesGamma E₁ G A →
    StableGamma D₁ E₁ (S \ A) →
    PreservesGamma D₂ F (insert w A) → PreservesGamma E₂ G (insert w A) →
    StableGamma D₂ E₂ (S \ insert w A) →
    MeromorphicEq (fun s => ∏ v ∈ A, (F v).gamma s)
      (fun s => ∏ v ∈ A, (G v).gamma s) ∧
    MeromorphicEq (F w).gamma (G w).gamma

/-- The complete generic finite-exceptional-set engine, split into focused
components for proofs. Actual arithmetic/automorphic adapters are separate. -/
def FiniteFunctionalEquationComparisonStatement : Prop :=
  EulerTailComparisonStatement.{u} ∧ FiniteGammaComparisonStatement.{u} ∧
    GlobalFiniteGammaComparisonStatement.{u} ∧ FiniteBlockCancellationStatement.{u} ∧
    TwoTwistIsolationStatement.{u}

end Langlands.Global.FunctionalEquationComparison
