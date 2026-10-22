import Langlands.Representation.Smooth.Admissibility.EmbeddingStatement
import Langlands.Representation.Smooth.FixedVectors.Definitions
import Mathlib.RingTheory.Noetherian.Basic

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

variable {ρ : Representation R G V} {σ : Representation R G W}

/-- Admissibility passes through an injective intertwiner over a Noetherian ring. -/
theorem isAdmissible_of_injective [IsNoetherianRing R] (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) (hσ : IsAdmissible σ) : IsAdmissible ρ := by
  refine ⟨?_, ?_⟩
  · intro v
    obtain ⟨K, hK⟩ := hσ.1 (f v)
    refine ⟨K, ?_⟩
    change ∀ k : K, ρ (k : G) v = v
    intro k
    apply hf
    rw [f.isIntertwining]
    exact hK k
  · intro K
    let : Module.Finite R (fixedVectors σ K.toSubgroup) := hσ.2 K
    apply Module.Finite.of_injective (fixedVectorsMap f K.toSubgroup)
    intro v w hvw
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hvw

theorem admissibleSubrepresentation :
    AdmissibleSubrepresentationStatement (R := R) (G := G) (V := V) (W := W) := by
  intro _ ρ σ f hf hσ
  exact isAdmissible_of_injective f hf hσ

end Langlands
