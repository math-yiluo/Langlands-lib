import Langlands.Global.Arithmetic.IdeleSUnits
import Langlands.Global.Adelic

/-! # Arithmetic data for an S-unit cover of idele power classes -/

noncomputable section

namespace Langlands.Global.Arithmetic.IdelePowerQuotientCover

open NumberField
open Langlands.Global.Arithmetic.IdeleSUnits

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- A finite set of finite places with global uniformizers outside the set. -/
def places : Finset (FinitePlace K) :=
  (exists_hasGlobalUniformizers K ∅).choose

theorem hasGlobalUniformizers_places : HasGlobalUniformizers K (places K) :=
  (exists_hasGlobalUniformizers K ∅).choose_spec.2

/-- Principal ideles together with the chosen S-unit idele subgroup generate all ideles. -/
theorem principal_sup :
    principalIdeles K ⊔ sUnitIdeles K (places K) = ⊤ :=
  principal_sup_sUnitIdeles (hasGlobalUniformizers_places K)

/-- For any finite S, the principal ideles inside the S-unit idele subgroup are
finitely generated, since they are the image of the S-unit group. -/
theorem principal_intersection_fg (S : Finset (FinitePlace K)) :
    ((principalIdeles K).subgroupOf (sUnitIdeles K S)).FG := by
  change ((IdeleGroup.principalSubgroup (𝓞 K) K).subgroupOf (sUnitIdeles K S)).FG
  rw [← range_sUnitsToIdeles]
  have : Group.FG (Langlands.Global.Arithmetic.SUnitIndex.sUnits K S) :=
    Group.fg_iff_monoid_fg.mpr inferInstance
  exact (Group.fg_iff_subgroup_fg _).mp inferInstance

end Langlands.Global.Arithmetic.IdelePowerQuotientCover
