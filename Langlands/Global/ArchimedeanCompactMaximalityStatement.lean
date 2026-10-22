import Langlands.Global.AdelicGL
import Langlands.Global.ArchimedeanCompact

/-!
# Maximality of the standard archimedean compact subgroup

This is the remaining maximality statement for the constructed subgroup in the
actual completion-based group. Its compactness is already proved separately.
-/

universe u

namespace Langlands.Global

/-- Every compact subgroup containing the standard orthogonal/unitary subgroup
equals it. This statement includes all natural ranks, including zero. -/
def StandardInfiniteCompactMaximalityStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ U : Subgroup (InfiniteAdelicGL K n),
    IsCompact (U : Set (InfiniteAdelicGL K n)) →
      standardInfiniteCompact K n ≤ U →
        U = standardInfiniteCompact K n

end Langlands.Global
