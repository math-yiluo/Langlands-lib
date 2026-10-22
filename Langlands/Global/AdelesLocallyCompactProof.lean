import Langlands.Global.CompletionResidue
import Langlands.Global.AdeleQuotientStatement
import Mathlib.Topology.Algebra.Valued.LocallyCompact

noncomputable section

open scoped Valued RestrictedProduct

universe u

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (v : FinitePlace K)

private theorem normIntegers_eq_adic :
    LocalGalois.baseIntegers (FiniteCompletion K v) = v.adicCompletionIntegers K := by
  ext x
  change ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1
  exact Valued.toNormedField.norm_le_one_iff

private theorem compact_adicIntegers :
    CompactSpace (v.adicCompletionIntegers K) := by
  have : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
    rw [← normIntegers_eq_adic K v]
    exact CompletionResidue.finite_residueField K v
  have : CompleteSpace (v.adicCompletionIntegers K) :=
    (Valued.isClosed_valuationSubring (FiniteCompletion K v)).isComplete.completeSpace_coe
  exact (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := FiniteCompletion K v) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
    ⟨inferInstanceAs (CompleteSpace (v.adicCompletionIntegers K)),
      inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)),
      inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))⟩

/-- The finite adele ring of a number field is locally compact for its
restricted-product topology. -/
theorem finiteAdeles_locallyCompactSpace : LocallyCompactSpace (FiniteAdeles K) := by
  have : ∀ v : FinitePlace K, CompactSpace (v.adicCompletionIntegers K) :=
    fun v ↦ compact_adicIntegers K v
  have : Fact (∀ v : FinitePlace K,
      IsOpen (v.adicCompletionIntegers K : Set (FiniteCompletion K v))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  exact inferInstanceAs (LocallyCompactSpace
    (Πʳ v : FinitePlace K, [FiniteCompletion K v, v.adicCompletionIntegers K]))

/-- The full adele ring of a number field is locally compact for its product
of archimedean and finite restricted-product topologies. -/
theorem adeles_locallyCompactSpace : LocallyCompactSpace (Adeles K) := by
  have := finiteAdeles_locallyCompactSpace K
  exact inferInstanceAs (LocallyCompactSpace (InfiniteAdeles K × FiniteAdeles K))

/-- Proof of the published local compactness statement for number-field adeles. -/
theorem adelesLocallyCompact : AdelesLocallyCompactStatement K :=
  adeles_locallyCompactSpace K

end Langlands.Global
