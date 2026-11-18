import Langlands.Representation.Archimedean.RealTemperedCommutantReduction

/-!
# The tied scalar commutant: lists with and without a discrete-series block

`RealTemperedScalarCommutantStatement` asks for a scalar simultaneous commutant on the real
standard module of every list of real blocks of total rank `n` with equal real exponents. This
module splits it into two open statements. The first is for lists without a discrete-series
block, that is, without an induction block of nonzero weight. The second is for lists with at
least one such block. Together they imply the target.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-- A real block is a discrete-series block when it is an induction block of nonzero weight.
A character block and an induction block of weight `0` are not. -/
def IsRealDiscreteSeriesBlock : RealBlock → Prop
  | .character _ => False
  | .induced d => d.weight ≠ 0

/-- The scalar simultaneous compact/Lie commutant for every rank-correct list of real blocks
whose real exponents are equal and which has no discrete-series block. This is an open
prerequisite. -/
def RealTiedNondiscreteScalarCommutantStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    (∀ x ∈ ds, ∀ y ∈ ds, realBlockExponent x = realBlockExponent y) →
    (∀ x ∈ ds, ¬ IsRealDiscreteSeriesBlock x) →
      RealTemperedCommutantReduction.HasScalarCommutant n ds

/-- The scalar simultaneous compact/Lie commutant for every rank-correct list of real blocks
whose real exponents are equal and which has at least one discrete-series block. This is an
open prerequisite. -/
def RealTiedDiscreteScalarCommutantStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    (∀ x ∈ ds, ∀ y ∈ ds, realBlockExponent x = realBlockExponent y) →
    (∃ x ∈ ds, IsRealDiscreteSeriesBlock x) →
      RealTemperedCommutantReduction.HasScalarCommutant n ds

/-- The two cases imply the scalar commutant statement for all tied lists. -/
theorem realTemperedScalarCommutant_of_cases
    (h₁ : RealTiedNondiscreteScalarCommutantStatement)
    (h₂ : RealTiedDiscreteScalarCommutantStatement) :
    RealTemperedScalarCommutantStatement := by
  intro n ds hr he
  by_cases h : ∃ x ∈ ds, IsRealDiscreteSeriesBlock x
  · exact h₂ n ds hr he h
  · exact h₁ n ds hr he fun x hx hxd => h ⟨x, hx, hxd⟩

end Langlands.Archimedean
