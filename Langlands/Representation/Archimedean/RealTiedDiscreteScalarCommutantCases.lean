import Langlands.Representation.Archimedean.RealTiedScalarCommutantCases

/-!
# The tied discrete-series scalar commutant: separated and coincident exponents

`RealTiedDiscreteScalarCommutantStatement` asks for a scalar simultaneous commutant on the real
standard module of every rank-correct list of real blocks with equal real exponents and at least
one discrete-series block. This module splits it into two open statements. The first is for
lists in which every block with the same complex exponent as a discrete-series block is an
induction block of the same absolute weight. The second is for the remaining lists. Together they imply the target.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-- The complex exponent `t` of a real block: `t` for the character `sgn^ε |·|^t` of `GL_1(ℝ)`
and for the block of `GL_2(ℝ)` induced from the character `(z/|z|)^m |z|^(2t)` of `ℂ^×`. -/
def realBlockComplexExponent : RealBlock → ℂ
  | .character d => d.exponent
  | .induced d => d.exponent

/-- The absolute weight of a real block: `none` for a character block and `some |m|` for the
induction block of weight `m`. -/
def realBlockAbsWeight : RealBlock → Option ℕ
  | .character _ => none
  | .induced d => some d.weight.natAbs

/-- A list of real blocks has separated discrete exponents when every block with the same
complex exponent as a discrete-series block of the list is an induction block with the same
absolute weight. -/
def IsRealDiscreteExponentSeparated (ds : List RealBlock) : Prop :=
  ∀ x ∈ ds, IsRealDiscreteSeriesBlock x → ∀ y ∈ ds,
    realBlockComplexExponent y = realBlockComplexExponent x →
      realBlockAbsWeight y = realBlockAbsWeight x

/-- The scalar simultaneous compact/Lie commutant for every rank-correct list of real blocks
with equal real exponents, at least one discrete-series block and separated discrete exponents.
This is an open prerequisite. -/
def RealTiedDiscreteSeparatedScalarCommutantStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    (∀ x ∈ ds, ∀ y ∈ ds, realBlockExponent x = realBlockExponent y) →
    (∃ x ∈ ds, IsRealDiscreteSeriesBlock x) →
    IsRealDiscreteExponentSeparated ds →
      RealTemperedCommutantReduction.HasScalarCommutant n ds

/-- The scalar simultaneous compact/Lie commutant for every rank-correct list of real blocks
with equal real exponents, at least one discrete-series block, and a block with the same complex
exponent as a discrete-series block but a different shape. This is an open prerequisite. -/
def RealTiedDiscreteCoincidentScalarCommutantStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    (∀ x ∈ ds, ∀ y ∈ ds, realBlockExponent x = realBlockExponent y) →
    (∃ x ∈ ds, IsRealDiscreteSeriesBlock x) →
    ¬ IsRealDiscreteExponentSeparated ds →
      RealTemperedCommutantReduction.HasScalarCommutant n ds

/-- The two cases imply the scalar commutant statement for all tied lists with a
discrete-series block. -/
theorem realTiedDiscreteScalarCommutant_of_cases
    (ha : RealTiedDiscreteSeparatedScalarCommutantStatement)
    (hb : RealTiedDiscreteCoincidentScalarCommutantStatement) :
    RealTiedDiscreteScalarCommutantStatement := by
  intro n ds hr he hd
  by_cases hs : IsRealDiscreteExponentSeparated ds
  · exact ha n ds hr he hd hs
  · exact hb n ds hr he hd hs

end Langlands.Archimedean
