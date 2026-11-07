import Langlands.Algebra.CyclicNormCommutator
import Langlands.Algebra.DivisionFieldEmbeddingsProof

/-! Norm-one units of cyclic subfields are single commutators in a central division algebra. -/

noncomputable section

namespace Langlands.CentralDivision

universe uK uL uD

open scoped commutatorElement

variable {K : Type uK} [Field K] {D : Type uD} [DivisionRing D]
  [Algebra K D] [FiniteDimensional K D] [Algebra.IsCentral K D]
  {L : Type uL} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- A unit implementing the specified automorphism of an embedded finite field. -/
def implementingUnit (ι : L →ₐ[K] D) (σ : L ≃ₐ[K] L) : Dˣ :=
  Classical.choose (exists_unit_conj K D L (ι.comp σ.toAlgHom) ι)

theorem implementingUnit_conj (ι : L →ₐ[K] D) (σ : L ≃ₐ[K] L) (a : L) :
    (implementingUnit ι σ : D) * ι a * ((implementingUnit ι σ)⁻¹ : Dˣ) =
      ι (σ a) := by
  exact (Classical.choose_spec (exists_unit_conj K D L (ι.comp σ.toAlgHom) ι) a).symm

variable [IsGalois K L]

/-- An embedded cyclic norm-one unit is a commutator with the constructed implementing unit. -/
theorem exists_commutator_with_implementingUnit_of_norm_eq_one
    (ι : L →ₐ[K] D) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (x : Lˣ)
    (hx : Algebra.norm K (x : L) = 1) :
    ∃ v : Dˣ, Units.map ι.toMonoidHom x = ⁅v, implementingUnit ι σ⁆ :=
  Langlands.CyclicNorm.exists_commutator_of_norm_eq_one ι σ hσ
    (implementingUnit ι σ) (implementingUnit_conj ι σ) x hx

/-- No generator or implementing unit is supplied for a finite cyclic Galois subfield. -/
theorem exists_commutator_of_cyclic_field_norm_eq_one [IsCyclic (L ≃ₐ[K] L)]
    (ι : L →ₐ[K] D) (x : Lˣ) (hx : Algebra.norm K (x : L) = 1) :
    ∃ v u : Dˣ, Units.map ι.toMonoidHom x = ⁅v, u⁆ := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  obtain ⟨v, hv⟩ :=
    exists_commutator_with_implementingUnit_of_norm_eq_one ι σ hσ x hx
  exact ⟨v, implementingUnit ι σ, hv⟩

/-- The image of an actual cyclic field norm-one unit is in the unit commutator subgroup. -/
theorem map_mem_commutator_of_cyclic_field_norm_eq_one [IsCyclic (L ≃ₐ[K] L)]
    (ι : L →ₐ[K] D) (x : Lˣ) (hx : Algebra.norm K (x : L) = 1) :
    Units.map ι.toMonoidHom x ∈ commutator Dˣ := by
  obtain ⟨v, u, h⟩ := exists_commutator_of_cyclic_field_norm_eq_one ι x hx
  rw [h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) (Subgroup.mem_top u)

end Langlands.CentralDivision
