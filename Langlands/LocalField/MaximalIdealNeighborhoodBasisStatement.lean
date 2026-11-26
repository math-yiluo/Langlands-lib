import Langlands.LocalField.ResidueNormalization

/-! # The maximal-ideal neighborhood basis of a local field -/

namespace Langlands.LocalField

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The powers of the maximal ideal of the valuation ring, viewed in the
field, are compact and open and form a neighborhood basis of zero. -/
def MaximalIdealNeighborhoodBasisStatement : Prop :=
  let powers : ℕ → Set F := fun n =>
    (Subtype.val : FML.ringOfIntegers F → F) ''
      ((IsLocalRing.maximalIdeal (FML.ringOfIntegers F) ^ n :
        Ideal (FML.ringOfIntegers F)) : Set (FML.ringOfIntegers F))
  (∀ n, IsCompact (powers n) ∧ IsOpen (powers n)) ∧
    (nhds (0 : F)).HasBasis (fun _ : ℕ => True) powers

end Langlands.LocalField
