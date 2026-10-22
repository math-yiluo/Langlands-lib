import Langlands.Representation.Smooth.Admissibility.CofinalStatement
import Mathlib.RingTheory.Noetherian.Basic

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

variable {ρ : Representation R G V}

/-- Finite generation of fixed vectors passes from a smaller to a larger subgroup
over Noetherian coefficients. -/
theorem finite_fixedVectors_of_le [IsNoetherianRing R] {H K : Subgroup G}
    (hHK : H ≤ K) [Module.Finite R (fixedVectors ρ H)] :
    Module.Finite R (fixedVectors ρ K) := by
  have hfixed : fixedVectors ρ K ≤ fixedVectors ρ H := by
    intro v hv
    change ∀ h : H, ρ (h : G) v = v
    intro h
    exact hv ⟨h, hHK h.property⟩
  exact Module.Finite.of_injective (Submodule.inclusion hfixed)
    (Submodule.inclusion_injective hfixed)

variable [TopologicalSpace G]

/-- A cofinal family can provide all fixing subgroups for smooth vectors. -/
theorem isSmoothVector_iff_of_cofinal (S : Set (OpenSubgroup G))
    (hS : ∀ K : OpenSubgroup G, ∃ L ∈ S, L ≤ K) (v : V) :
    IsSmoothVector ρ v ↔ ∃ K ∈ S, v ∈ fixedVectors ρ K.toSubgroup := by
  constructor
  · rintro ⟨K, hv⟩
    obtain ⟨L, hLS, hLK⟩ := hS K
    refine ⟨L, hLS, ?_⟩
    change ∀ l : L, ρ (l : G) v = v
    intro l
    exact hv ⟨l, hLK l.property⟩
  · rintro ⟨K, _, hv⟩
    exact ⟨K, hv⟩

theorem isSmooth_iff_of_cofinal (S : Set (OpenSubgroup G))
    (hS : ∀ K : OpenSubgroup G, ∃ L ∈ S, L ≤ K) :
    IsSmooth ρ ↔ ∀ v : V, ∃ K ∈ S, v ∈ fixedVectors ρ K.toSubgroup := by
  constructor
  · intro hρ v
    exact (isSmoothVector_iff_of_cofinal S hS v).mp (hρ v)
  · intro hρ v
    exact (isSmoothVector_iff_of_cofinal S hS v).mpr (hρ v)

/-- Over a Noetherian ring it suffices to test admissibility on a family
containing a subgroup of every open subgroup. -/
theorem isAdmissible_iff_of_cofinal [IsNoetherianRing R] (S : Set (OpenSubgroup G))
    (hS : ∀ K : OpenSubgroup G, ∃ L ∈ S, L ≤ K) :
    IsAdmissible ρ ↔
      IsSmooth ρ ∧ ∀ K ∈ S, Module.Finite R (fixedVectors ρ K.toSubgroup) := by
  constructor
  · intro hρ
    exact ⟨hρ.1, fun K _ => hρ.2 K⟩
  · rintro ⟨hsmooth, hfinite⟩
    refine ⟨hsmooth, ?_⟩
    intro K
    obtain ⟨L, hLS, hLK⟩ := hS K
    let : Module.Finite R (fixedVectors ρ L.toSubgroup) := hfinite L hLS
    exact finite_fixedVectors_of_le (show L.toSubgroup ≤ K.toSubgroup from hLK)

theorem admissibleCofinal :
    AdmissibleCofinalStatement (R := R) (G := G) (V := V) := by
  intro _ S hS ρ
  exact isAdmissible_iff_of_cofinal S hS

end Langlands
