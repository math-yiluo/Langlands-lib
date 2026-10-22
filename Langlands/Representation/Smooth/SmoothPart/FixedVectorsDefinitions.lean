import Langlands.Representation.Smooth.SmoothPart.Definitions

/-! # Open-subgroup fixed vectors of the smooth part -/

noncomputable section

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

/-- Passing to the smooth part preserves the vectors fixed by an open subgroup. -/
def smoothPartFixedVectorsEquiv (ρ : Representation R G V) (K : OpenSubgroup G) :
    fixedVectors (smoothPart ρ) K.toSubgroup ≃ₗ[R] fixedVectors ρ K.toSubgroup where
  toFun v := ⟨v.val.val, fun k => congrArg Subtype.val (v.property k)⟩
  invFun v := ⟨⟨v.val, ⟨K, v.property⟩⟩, fun k => Subtype.ext (v.property k)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Langlands
