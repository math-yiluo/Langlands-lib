import Langlands.Algebra.ReducedNormSubfield
import Langlands.Algebra.CyclicFieldNormCommutator
import Langlands.Algebra.BinaryReducedNorm
import Mathlib.GroupTheory.Abelianization.Defs

/-! Canonical reduced-norm-one units in cyclic subfields are commutators. -/

noncomputable section

namespace Langlands.CentralDivision

universe u uL

open Langlands.CentralSimple Langlands.BinaryElementary.Reduced
open scoped commutatorElement

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  {L : Type uL} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The image of the genuine field-norm-one unit subgroup under an actual field embedding. -/
def fieldNormOneImage (ι : L →ₐ[K] D) : Subgroup Dˣ :=
  (Units.map (Algebra.norm K : L →* K)).ker.map (Units.map ι.toMonoidHom)

/-- On a field of reduced degree, canonical coefficient norm is the actual field norm on units. -/
theorem coefficientNorm_comp_field (ι : L →ₐ[K] D)
    (hdeg : Module.finrank K L = reducedDegree K D) :
    (coefficientNorm K D).comp (Units.map ι.toMonoidHom) =
      Units.map (Algebra.norm K : L →* K) := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  exact reducedNorm_eq_field_norm K D ι hdeg (x : L)

/-- The canonical norm kernel in the field-unit image is exactly the image of field-norm-one units. -/
theorem fieldNormOneImage_eq_range_inf_ker (ι : L →ₐ[K] D)
    (hdeg : Module.finrank K L = reducedDegree K D) :
    fieldNormOneImage ι =
      (Units.map ι.toMonoidHom).range ⊓ (coefficientNorm K D).ker := by
  rw [fieldNormOneImage, ← coefficientNorm_comp_field ι hdeg,
    ← MonoidHom.comap_ker, Subgroup.map_comap_eq]

/-- Every unit commutator has canonical reduced norm one, over any base field. -/
theorem commutator_le_ker_coefficientNorm :
    commutator Dˣ ≤ (coefficientNorm K D).ker :=
  Abelianization.commutator_subset_ker _

section Cyclic

variable [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-- Field-norm-one units of an actual cyclic subfield are single commutators. -/
theorem exists_commutator_of_mem_fieldNormOneImage (ι : L →ₐ[K] D)
    {x : Dˣ} (hx : x ∈ fieldNormOneImage ι) :
    ∃ v u : Dˣ, x = ⁅v, u⁆ := by
  obtain ⟨a, ha, rfl⟩ := hx
  apply exists_commutator_of_cyclic_field_norm_eq_one ι a
  exact congrArg Units.val ha

/-- The image of cyclic field-norm-one units is contained in the actual unit commutator subgroup. -/
theorem fieldNormOneImage_le_commutator (ι : L →ₐ[K] D) :
    fieldNormOneImage ι ≤ commutator Dˣ := by
  intro x hx
  obtain ⟨v, u, h⟩ := exists_commutator_of_mem_fieldNormOneImage ι hx
  rw [h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) (Subgroup.mem_top u)

/-- An original unit in a cyclic field of reduced degree with canonical reduced norm one is a commutator. -/
theorem exists_commutator_of_field_image_reducedNorm_eq_one (ι : L →ₐ[K] D)
    (hdeg : Module.finrank K L = reducedDegree K D) {x : Dˣ}
    (hx : x ∈ (Units.map ι.toMonoidHom).range)
    (hnorm : coefficientNorm K D x = 1) :
    ∃ v u : Dˣ, x = ⁅v, u⁆ := by
  apply exists_commutator_of_mem_fieldNormOneImage ι
  rw [fieldNormOneImage_eq_range_inf_ker ι hdeg]
  exact ⟨hx, hnorm⟩

/-- Inside this cyclic field image, the canonical norm kernel is precisely the commutator intersection. -/
theorem range_inf_ker_coefficientNorm_eq_range_inf_commutator (ι : L →ₐ[K] D)
    (hdeg : Module.finrank K L = reducedDegree K D) :
    (Units.map ι.toMonoidHom).range ⊓ (coefficientNorm K D).ker =
      (Units.map ι.toMonoidHom).range ⊓ commutator Dˣ := by
  apply le_antisymm
  · apply le_inf inf_le_left
    rw [← fieldNormOneImage_eq_range_inf_ker ι hdeg]
    exact fieldNormOneImage_le_commutator ι
  · exact inf_le_inf_left _ commutator_le_ker_coefficientNorm

end Cyclic

end Langlands.CentralDivision
