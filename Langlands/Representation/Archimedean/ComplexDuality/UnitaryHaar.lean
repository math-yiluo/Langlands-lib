import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Langlands.Global.ArchimedeanCompact
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral

/-!
# Haar measure on `U(n)`
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator
open MeasureTheory

namespace Langlands.Archimedean.ComplexDuality

set_option backward.isDefEq.respectTransparency false

/-! ## The compact group `U(n)` -/

theorem unitaryCompact_eq_range (n : ℕ) :
    (unitaryCompact ℂ n : Set (Langlands.GeneralLinear n ℂ)) =
      Set.range (Unitary.toUnits :
        Matrix.unitaryGroup (Fin n) ℂ → Langlands.GeneralLinear n ℂ) := by
  ext g
  constructor
  · intro hg
    exact ⟨⟨(g : Matrix (Fin n) (Fin n) ℂ), hg⟩, Units.ext rfl⟩
  · rintro ⟨k, rfl⟩
    exact k.2

theorem isCompact_unitaryCompact (n : ℕ) :
    IsCompact (unitaryCompact ℂ n : Set (Langlands.GeneralLinear n ℂ)) := by
  rw [unitaryCompact_eq_range]
  exact isCompact_range continuous_unitary_toUnits

instance compactSpace_unitaryCompact (n : ℕ) : CompactSpace (unitaryCompact ℂ n) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryCompact n)

/-- The Borel σ-algebra on `U(n)`. -/
scoped instance unitaryMeasurableSpace (n : ℕ) : MeasurableSpace (unitaryCompact ℂ n) :=
  borel _

scoped instance unitaryBorelSpace (n : ℕ) : BorelSpace (unitaryCompact ℂ n) := ⟨rfl⟩


/-- The Haar probability measure on `U(n)`. -/
def unitaryHaar (n : ℕ) : Measure (unitaryCompact ℂ n) :=
  Measure.haarMeasure ⊤

instance (n : ℕ) : IsProbabilityMeasure (unitaryHaar n) := by
  constructor
  rw [unitaryHaar, ← TopologicalSpace.PositiveCompacts.coe_top]
  exact Measure.haarMeasure_self

instance (n : ℕ) : (unitaryHaar n).IsHaarMeasure := by
  unfold unitaryHaar
  infer_instance

instance (n : ℕ) : (unitaryHaar n).IsMulLeftInvariant := by
  unfold unitaryHaar
  infer_instance

/-- On the compact group `U(n)` the Haar probability measure is also right invariant: its right
translate is again a Haar probability measure, hence equal to it. -/
instance (n : ℕ) : (unitaryHaar n).IsMulRightInvariant := by
  constructor
  intro g
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Continuous functions on `U(n)` are integrable. -/
theorem integrable_unitaryHaar {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : unitaryCompact ℂ n → E} (hf : Continuous f) : Integrable f (unitaryHaar n) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- A continuous nonnegative function on `U(n)` that is nonzero somewhere has positive
integral. -/
theorem integral_unitaryHaar_pos {n : ℕ} {f : unitaryCompact ℂ n → ℝ} (hf : Continuous f)
    (h0 : 0 ≤ f) {k : unitaryCompact ℂ n} (hk : f k ≠ 0) : 0 < ∫ x, f x ∂unitaryHaar n :=
  hf.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace f) h0 hk

end Langlands.Archimedean.ComplexDuality
