import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Tensor.Finite
import Mathlib.Data.List.OfFn

/-! # Actual integral cuspidal Jacquet words -/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- An integer word is realized on the twist line through `A` when an actual
supercuspidal tensor with those rank-indexed classes is a subquotient of an
actual normalized upper Jacquet module of `π`. -/
def IntegralCuspidalJacquetWord (m n : ℕ) :
    letI := T.topology
    SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m) →
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) →
        List ℤ → Prop :=
  letI := T.topology
  fun A π w =>
    ∃ (B : BlockShape n)
      (C : ∀ i : Fin B.length,
        SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := B.size i))
      (e : Fin B.length → ℤ),
      w = List.ofFn e ∧
        (∀ i : Fin B.length,
          (⟨B.size i, (C i).isoClass⟩ :
            Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
              ⟨m, T.supercuspidalClassRealPowerTwist m (e i : ℝ) A.isoClass⟩) ∧
        SmoothRep.IsSubquotient
          (FiniteTensor.externalSmoothObject (fun i => (C i).obj))
          ((T.normalizedJacquetFunctor B).obj π)

end Langlands.Classification
