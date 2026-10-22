import Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
import Langlands.Representation.Smooth.FixedVectors.Definitions
import Mathlib.RingTheory.Finiteness.Basic

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

variable {ρ : Representation R G V} {σ : Representation R G W}

/-- Equivalence transports admissibility without a Noetherian hypothesis. -/
theorem isAdmissible_of_equiv (e : ρ.Equiv σ) (hρ : IsAdmissible ρ) :
    IsAdmissible σ := by
  refine ⟨?_, ?_⟩
  · intro w
    obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
    obtain ⟨K, hK⟩ := hρ.1 v
    refine ⟨K, ?_⟩
    change ∀ k : K, σ (k : G) (e v) = e v
    intro k
    calc
      σ (k : G) (e v) = e (ρ (k : G) v) :=
        (Representation.IntertwiningMap.isIntertwining ρ σ
          e.toIntertwiningMap (k : G) v).symm
      _ = e v := congrArg e (hK k)
  · intro K
    exact (Module.Finite.equiv_iff (fixedVectorsEquiv e K.toSubgroup)).mp (hρ.2 K)

theorem isAdmissible_iff_of_equiv (e : ρ.Equiv σ) :
    IsAdmissible ρ ↔ IsAdmissible σ :=
  ⟨isAdmissible_of_equiv e, isAdmissible_of_equiv e.symm⟩

theorem admissibleEquivalence :
    AdmissibleEquivalenceStatement (R := R) (G := G) (V := V) (W := W) := by
  intro ρ σ e
  exact isAdmissible_iff_of_equiv e

end Langlands
