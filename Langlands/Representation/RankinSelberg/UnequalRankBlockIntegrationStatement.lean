import Langlands.Representation.RankinSelberg.UnequalRankBlockMatrix
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.HarmonicAnalysis.RowFourier
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Block matrices and integration helpers for unequal-rank JPSS integrals

These proposition definitions isolate the nine ready helper interfaces from
the adjacent-block draft. Each component quantifies its complete source
telescope. The aggregate has no additional premise and asserts no support
existence, Fourier existence or adjacent-span comparison.
-/

noncomputable section

namespace Langlands.RankinSelberg.AdjacentBlockReduction

open MeasureTheory HarmonicAnalysis Whittaker

-- Retain the source names of hypotheses used only in the future proofs.
set_option linter.unusedVariables false in
/-- A uniformly compactly supported family of translates has one coefficient
representing every scalar fiber integral in the original algebraic model. -/
def CoefficientFiberIntegralStatement.{uX, uP, uG, uV} : Prop :=
  ∀ {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {P : Type uP}
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {N : Subgroup G} {θ : N →* ℂˣ} (ℓ : functionals N θ ρ)
    (U : X → G) (hU : Continuous U) (B : P → G)
    (f : (coefficientModel ρ ℓ).toSubmodule)
    (hc : HasCompactSupport (fun x p => f.val.val (B p * U x))),
    ∃ f₀ : (coefficientModel ρ ℓ).toSubmodule, ∀ p,
      Integrable (fun x => f.val.val (B p * U x)) μ ∧
      f₀.val.val (B p) = ∫ x, f.val.val (B p * U x) ∂μ

/-- Splitting the final rectangular row is multiplication by the actual
last-row rectangular unipotent on the right. -/
def UnequalRankMatrixSnocStatement.{uF} : Prop :=
  ∀ {F : Type uF} [Field F] {n : ℕ} (j k : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (Y : Matrix (Fin j) (Fin (n + 1)) F) (x : Fin (n + 1) → F),
    unequalRankMatrix (j + 1) k g (Fin.snoc Y x) =
      unequalRankMatrix (j + 1) k g (Fin.snoc Y 0) *
        rectangularUnipotent (j + 1) k (Fin.snoc 0 x)

/-- The transported block matrix has the concrete diagonal and rectangular
entry formula of the published unequal-rank matrix. -/
def BlockMatrixAtEntryStatement.{uF} : Prop :=
  ∀ {F : Type uF} [Field F] {n r : ℕ} (j k : ℕ)
    (hr : r = n + (j + k + 1))
    (g : Langlands.GeneralLinear (n + 1) F)
    (Y : Matrix (Fin j) (Fin (n + 1)) F) (a b : Fin (r + 1)),
    blockMatrixAt j k hr g Y a b =
      (if ha : a.val < n + 1 then
        if hb : b.val < n + 1 then g ⟨a.val, ha⟩ ⟨b.val, hb⟩ else 0
       else if a = b then 1 else 0) +
      (if ha : n + 1 ≤ a.val ∧ a.val < n + 1 + j then
        if hb : b.val < n + 1 then Y ⟨a.val - (n + 1), by omega⟩ ⟨b.val, hb⟩ else 0
       else 0)

/-- A zero final rectangular row gives the adjacent block matrix, with both
natural-number rank equalities retained. -/
def BlockMatrixAtSnocZeroStatement.{uF} : Prop :=
  ∀ {F : Type uF} [Field F] {n r : ℕ} (j k : ℕ)
    (h₁ : r = n + ((j + 1) + k + 1)) (h₂ : r = n + (j + (k + 1) + 1))
    (g : Langlands.GeneralLinear (n + 1) F)
    (Y : Matrix (Fin j) (Fin (n + 1)) F),
    blockMatrixAt (j + 1) k h₁ g (Fin.snoc Y 0) =
      blockMatrixAt j (k + 1) h₂ g Y

/-- The last-row rectangular unipotent depends continuously on its row. -/
def ContinuousLastRowUnipotentStatement.{uF} : Prop :=
  ∀ {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (n j k : ℕ),
    Continuous (fun x : Fin (n + 1) → F =>
      rectangularUnipotent (j + 1) k (Fin.snoc 0 x))

/-- Separating the final row preserves the supplied product Haar measure,
with the last row first in the resulting product. -/
def RectangularLastRowMeasurePreservingStatement.{uF} : Prop :=
  ∀ {F : Type uF} [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure] (j t : ℕ),
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => Fin t → F) (Fin.last j))
      (rectangularMeasure ν (j + 1) t)
      ((rowMeasure ν t).prod (rectangularMeasure ν j t))

set_option linter.unusedVariables false in
/-- Genuine Fubini for an explicitly integrable rectangular function, with
the last row integrated inside the preceding rows. -/
def RectangularIntegralLastRowStatement.{uF} : Prop :=
  ∀ {F : Type uF} [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure] (j t : ℕ)
    (f : Matrix (Fin (j + 1)) (Fin t) F → ℂ)
    (hf : Integrable f (rectangularMeasure ν (j + 1) t)),
    (∫ X, f X ∂rectangularMeasure ν (j + 1) t) =
      ∫ Y, ∫ x, f (Fin.snoc Y x) ∂rowMeasure ν t ∂rectangularMeasure ν j t

set_option linter.unusedVariables false in
/-- Smoothness and one compact support set uniform in the smaller-group
argument imply genuine scalar integrability in the rectangular variables. -/
def BlockCoefficientIntegrableStatement.{uF, uV} : Prop :=
  ∀ {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [MeasurableSpace F] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure] (n j k : ℕ)
    [BorelSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + (j + k + 1)) π)
    (f : (coefficientModel π ℓ).toSubmodule)
    (C : Set (Matrix (Fin j) (Fin (n + 1)) F)) (hC : IsCompact C)
    (hs : ∀ g X, f.val.val (unequalRankMatrix j k g X) ≠ 0 → X ∈ C)
    (g : Langlands.GeneralLinear (n + 1) F),
    Integrable (fun X => f.val.val (unequalRankMatrix j k g X))
      (rectangularMeasure ν j (n + 1))

/-- The existing totalized fixed-rank integral written as an outer quotient
integral of the rectangular coefficient integral, without a convergence premise. -/
def UnequalRankIntegralAtEqOuterStatement.{uF} : Prop :=
  ∀ {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
    {n r : ℕ} (j k : ℕ) (hr : r = n + (j + k + 1))
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (f : WhittakerFunctions ψ r) (f' : InverseWhittakerFunctions ψ n) (s : ℂ),
    unequalRankIntegralAt j k hr ψ abv μ ν f f' s =
      ∫ q, ((∫ X, f.val (blockMatrixAt j k hr q.out X) ∂ν) * f'.val q.out *
        determinantWeight abv q.out (s - ((j + k + 1 : ℕ) : ℂ) / 2)) ∂μ

/-- The nine universally quantified block-matrix and integration helpers,
in source order, with independent carrier universes and no extra premise. -/
def UnequalRankBlockIntegrationStatement.{uX, uP, uG, uF, uV} : Prop :=
  CoefficientFiberIntegralStatement.{uX, uP, uG, uV} ∧
  UnequalRankMatrixSnocStatement.{uF} ∧
  BlockMatrixAtEntryStatement.{uF} ∧
  BlockMatrixAtSnocZeroStatement.{uF} ∧
  ContinuousLastRowUnipotentStatement.{uF} ∧
  RectangularLastRowMeasurePreservingStatement.{uF} ∧
  RectangularIntegralLastRowStatement.{uF} ∧
  BlockCoefficientIntegrableStatement.{uF, uV} ∧
  UnequalRankIntegralAtEqOuterStatement.{uF}

end Langlands.RankinSelberg.AdjacentBlockReduction
