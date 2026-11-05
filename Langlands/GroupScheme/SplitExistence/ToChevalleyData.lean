import Langlands.GroupScheme.SplitExistence.ChevalleyLieData
import Langlands.GroupScheme.SplitExistence.CommutatorInt

/-! # From Lie relations to group commutator relations

Integral Chevalley data with Lie relations (`ChevalleyLieData`) give integral Chevalley data
(`ChevalleyData`): the group commutator relations are derived from the Lie relations `lie_e_e`
by `LieRootData.commutator`. -/

noncomputable section

universe u

namespace Langlands.GroupScheme.SplitExistence

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}

namespace ChevalleyLieData

variable (D : ChevalleyLieData P b)

/-- The root operators of integral Chevalley data with Lie relations. -/
def toLieRootData : LieRootData P where
  n := D.n
  wt := D.wt
  e := D.e
  e_zero := D.e_zero
  e_mul := D.e_mul
  e_eq_zero := D.e_eq_zero
  e_weight := D.e_weight
  e_one_map_ne_zero := D.e_one_map_ne_zero
  lie_e_e := D.lie_e_e

/-- **Integral Chevalley data from Lie relations.** All fields are copied; the commutator
relations are `LieRootData.commutator`. -/
def toChevalleyData [Finite J] : ChevalleyData P b where
  ℓ := D.ℓ
  ℓ_pos := D.ℓ_pos
  n := D.n
  wt := D.wt
  closure_range_wt := D.closure_range_wt
  e := D.e
  e_zero := D.e_zero
  e_mul := D.e_mul
  e_eq_zero := D.e_eq_zero
  e_weight := D.e_weight
  e_one_map_ne_zero := D.e_one_map_ne_zero
  φ := D.φ
  φ_natural := D.φ_natural
  φ_upper := D.φ_upper
  φ_lower := D.φ_lower
  φ_diag := D.φ_diag
  weyl_weight := D.weyl_weight
  weyl_conj := D.weyl_conj
  commutator := fun _ _ h hj hj' R _ s t => D.toLieRootData.commutator h hj hj' R s t

end ChevalleyLieData

end Langlands.GroupScheme.SplitExistence
