import Langlands.Representation.Archimedean.RealStandardEllipticCartanMatrix
import Langlands.Representation.Archimedean.RealStandardCompactTestTrace

/-! # Elliptic Cartan comparison from compact trace limits -/

noncomputable section

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace Langlands.Archimedean.RealStandardEllipticCartan

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean RealStandardCompactAverage

local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℝ

/-- At each separated regular Cartan point, a common filter of continuous compact tests
has zero trace limit below its elliptic rank and gives the normalized numerator at that rank. -/
def RealStandardEllipticCartanTraceLimitsStatement : Prop :=
  ∀ (r s : ℕ) (x : Coordinates r s), x ∈ separatedRegularCoordinates r s →
    ∃ (μ : Measure (K (2 * r + s))) (L : Filter C(K (2 * r + s), ℂ)) (c : ℂ),
      μ.IsHaarMeasure ∧ L.NeBot ∧ c ≠ 0 ∧
      (∀ {r' s' : ℕ} {ds : List RealBlock}
        {d : Fin r' → ComplexCharacterData} {b : Fin s' → RealCharacterData},
        realRank ds = 2 * r + s → ds.Perm (ofBlockData d b) →
          (∀ i, 0 < (d i).weight) → r' < r →
          Tendsto (compactTestTrace μ ds (cartanElement rfl x)) L (𝓝 0)) ∧
      (∀ {ds : List RealBlock} {d : Fin r → ComplexCharacterData} {b : Fin s → RealCharacterData},
        realRank ds = 2 * r + s → ds.Perm (ofBlockData d b) →
          (∀ i, 0 < (d i).weight) →
          Tendsto (compactTestTrace μ ds (cartanElement rfl x)) L
            (𝓝 (c * numerator (blockParameters d b) x)))

/-- Limits of the actual compact traces supply intertwiner-invariant Cartan evaluations. -/
theorem realStandardEllipticCartanEvaluation_of_traceLimits
    (hlimits : RealStandardEllipticCartanTraceLimitsStatement) :
    RealStandardEllipticCartanEvaluationStatement := by
  classical
  unfold RealStandardEllipticCartanTraceLimitsStatement at hlimits
  choose μ L c hμ hL hc hbelow htop using hlimits
  let A (r s : ℕ) (x : Coordinates r s) (ds : List RealBlock) :=
    if hx : x ∈ separatedRegularCoordinates r s then
      limUnder (L r s x hx) (compactTestTrace (μ r s x hx) ds (cartanElement rfl x))
    else 0
  let C (r s : ℕ) (x : Coordinates r s) :=
    if hx : x ∈ separatedRegularCoordinates r s then c r s x hx else 0
  refine ⟨fun {_ r s} _ ds x => A r s x ds, C, ?_, ?_, ?_, ?_⟩
  · intro r s x hx
    simpa only [C, dite_eq_left hx] using hc r s x hx
  · intro n ds es hn hm T hT hbij r s h x hx
    cases h
    have : (μ r s x hx).IsHaarMeasure := hμ r s x hx
    have he := realStandardCompactTestTrace (2 * r + s) (μ r s x hx) ds es hn hm
      T hT hbij (cartanElement rfl x)
    simp only [A, dite_eq_left hx, he]
  · intro n r s r' s' ds d b h hn hp hd hlt x hx
    cases h
    have : (L r s x hx).NeBot := hL r s x hx
    simpa only [A, dite_eq_left hx] using (hbelow r s x hx hn hp hd hlt).limUnder_eq
  · intro n r s ds d b h hn hp hd x hx
    cases h
    have : (L r s x hx).NeBot := hL r s x hx
    simpa only [A, C, dite_eq_left hx] using (htop r s x hx hn hp hd).limUnder_eq

/-- The compact trace limits yield the exact comparison for the original module lists. -/
theorem realStandardEllipticCartanComparison_of_traceLimits
    (hlimits : RealStandardEllipticCartanTraceLimitsStatement) :
    RealStandardEllipticCartanComparisonStatement :=
  realStandardEllipticCartanComparison_of_evaluation
    (realStandardEllipticCartanEvaluation_of_traceLimits hlimits)

end Langlands.Archimedean.RealStandardEllipticCartan
