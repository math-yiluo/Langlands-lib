import Langlands.Global.AdelicGL
import Langlands.Global.ArchimedeanCompact

/-! # Uniform neighborhood selection for compact conjugation -/

universe u
open Filter Topology
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- Every identity neighborhood contains the compact conjugation saturation
of an open identity neighborhood for the actual standard compact subgroup. -/
def CompactConjugationNeighborhoodStatement (K : Type u) [Field K] [NumberField K]
    (n : ℕ) : Prop :=
  ∀ U : Set (InfiniteAdelicGL K n), U ∈ 𝓝 (1 : InfiniteAdelicGL K n) →
    ∃ V : Set (InfiniteAdelicGL K n), V ∈ 𝓝 (1 : InfiniteAdelicGL K n) ∧
      IsOpen V ∧ V ⊆ U ∧
      {x | ∃ k : standardInfiniteCompact K n,
        ∃ y ∈ V, x = k.val * y * k.val⁻¹} ⊆ U

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CompactConjugationNeighborhoodStatement

end Langlands.Global.ArchimedeanGL
