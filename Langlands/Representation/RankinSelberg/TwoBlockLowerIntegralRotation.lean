import Langlands.Representation.RankinSelberg.TwoBlockDeformationFlat
import Langlands.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData

/-! The lower block rotation as an element of the canonical integral subgroup. -/

noncomputable section

open scoped BigOperators

namespace Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient

open GeneralLinear TwoBlockDeformation

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- Both the block rotation and its inverse have integral entries. -/
theorem blockRotation_mem_integralOpen :
    blockRotation h F.Carrier ∈ integralOpen F t := by
  rw [mem_integralOpen]
  constructor <;> intro i j
  · rw [blockRotation_apply]
    split <;> simp
  · rw [blockRotation_inv_apply]
    split <;> simp

/-- The inverse block rotation belongs to the same integral subgroup. -/
theorem blockRotation_inv_mem_integralOpen :
    (blockRotation h F.Carrier)⁻¹ ∈ integralOpen F t :=
  (integralOpen F t).inv_mem (blockRotation_mem_integralOpen F h)

/-- The actual block rotation bundled in the canonical integral subgroup. -/
def integralBlockRotation :
    letI := F.canonicalTopologicalData.topology
    integralOpen F t :=
  ⟨blockRotation h F.Carrier, blockRotation_mem_integralOpen F h⟩

@[simp]
theorem integralBlockRotation_coe :
    ((integralBlockRotation F h : integralOpen F t) :
      GeneralLinear (t + 1) F.Carrier) = blockRotation h F.Carrier := rfl

/-- Moving the inverse rotation into a right integral factor preserves membership. -/
theorem blockRotation_inv_mul_mem_integralOpen
    {k : GeneralLinear (t + 1) F.Carrier} (hk : k ∈ integralOpen F t) :
    (blockRotation h F.Carrier)⁻¹ * k ∈ integralOpen F t :=
  (integralOpen F t).mul_mem (blockRotation_inv_mem_integralOpen F h) hk

/-- Left multiplication by the inverse rotation carries the whole integral subgroup
onto itself. -/
theorem blockRotation_inv_mul_image_integralOpen :
    (fun k : GeneralLinear (t + 1) F.Carrier => (blockRotation h F.Carrier)⁻¹ * k) ''
      (integralOpen F t : Set (GeneralLinear (t + 1) F.Carrier)) =
      (integralOpen F t : Set (GeneralLinear (t + 1) F.Carrier)) := by
  ext k
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact blockRotation_inv_mul_mem_integralOpen F h hx
  · intro hk
    refine ⟨blockRotation h F.Carrier * k,
      (integralOpen F t).mul_mem (blockRotation_mem_integralOpen F h) hk, ?_⟩
    exact inv_mul_cancel_left _ _

end Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient
