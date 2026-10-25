import Langlands.Representation.RestrictedTensor.GroupTopology
import Langlands.Representation.Smooth.Definitions

/-! # Smooth vectors are fixed by a reference tail -/

universe uR uI uG uV

namespace Langlands.RestrictedTensor

variable {R : Type uR} [CommRing R] {ι : Type uI} {G : ι → Type uG}
variable [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
variable (H : ∀ i, Subgroup (G i)) (hH : ∀ i, IsOpen (H i : Set (G i)))
variable {V : Type uV} [AddCommGroup V] [Module R V]

include hH

/-- A smooth vector is fixed by all reference-group elements trivial on a finite set. -/
theorem exists_tailReferenceSubgroup_fixed_of_isSmoothVector
    (ρ : Representation R (RestrictedGroup G H) V) (v : V)
    (hv : Langlands.IsSmoothVector ρ v) :
    ∃ S : Finset ι, ∀ g ∈ tailReferenceSubgroup H S, ρ g v = v := by
  obtain ⟨U, hU⟩ := hv
  obtain ⟨S, hS⟩ := exists_tailReferenceSubgroup_le H hH U
  refine ⟨S, fun g hg => ?_⟩
  exact hU ⟨g, hS hg⟩

/-- A coordinate-form tail-fixing law for every vector of a smooth representation. -/
theorem exists_tail_fixed_of_isSmooth
    (ρ : Representation R (RestrictedGroup G H) V) (hρ : Langlands.IsSmooth ρ) (v : V) :
    ∃ S : Finset ι, ∀ g : RestrictedGroup G H,
      (∀ i ∈ S, g i = 1) → (∀ i ∉ S, g i ∈ H i) → ρ g v = v := by
  obtain ⟨S, hS⟩ := exists_tailReferenceSubgroup_fixed_of_isSmoothVector H hH ρ v (hρ v)
  exact ⟨S, fun g h1 hH => hS g ⟨h1, hH⟩⟩

end Langlands.RestrictedTensor
