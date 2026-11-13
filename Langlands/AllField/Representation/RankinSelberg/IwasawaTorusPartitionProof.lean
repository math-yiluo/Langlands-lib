import Langlands.Representation.RankinSelberg.IwasawaTorusPartitionProof
import Langlands.AllField.Representation.RankinSelberg.IwasawaTorusPartitionStatement
/-!
# Proof of the measurable uniformizer-coset partition of the diagonal torus

The valuation lemmas decompose every field unit uniquely as an integer power of
a uniformizing element times an integral unit. A group-theoretic lemma turns
such a decomposition, for a left-invariant measure giving the units mass one,
into the full coset partition of the finite product. The resulting countable
coset cover also supplies σ-finiteness of the normalized multiplicative Haar
measure.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding IwasawaTorusPartitionStatement iwasawaTorusPartition
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.GeneralLinear

universe uF

section Valuation

variable {E : Type*} [Field E] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation E Γ₀)

variable {v}

end Valuation

section Group

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

end Group

/-- The diagonal torus is the disjoint union of the measurable uniformizer cosets of its
integral units, each of normalized product Haar mass one. -/
theorem iwasawaTorusPartition : IwasawaTorusPartitionStatement.{uF} := by
  intro F _ T m
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace Fˣ := borel Fˣ
  have : BorelSpace Fˣ := ⟨rfl⟩
  intro ϖ hϖ
  have hK : MeasurableSet
      (integralUnits (ValuativeRel.valuation F).integer : Set Fˣ) :=
    (integralUnits_isOpen _ Valuation.isOpen_integer).measurableSet
  have hcover := exists_zpow_mul_integralUnits hϖ
  have : SigmaFinite (localMultiplicativeHaar F) :=
    sigmaFinite_of_zpow_cover _ _ (by rw [localMultiplicativeHaar_integerUnits]; simp) ϖ
      hcover
  exact zpow_coset_partition (localMultiplicativeHaar F) _ hK
    (localMultiplicativeHaar_integerUnits F) ϖ hcover
    (fun _ _ _ _ hu hu' h => zpow_eq_of_mul_integralUnits hϖ hu hu' h) m

end Langlands.AllField.RankinSelberg
