import Langlands.Geometry.FormalGroup.HarrisComponentQuotient
import Langlands.Geometry.FormalGroup.DivisionOrder
import Mathlib.Algebra.Group.Subgroup.MulOpposite

/-! # Integral units in the split valuation kernel -/

noncomputable section
universe u

namespace Langlands.FormalGroup.Harris
open MulOpposite ValuativeRel Langlands.CentralDivision Langlands.Shimura.LocalDivision
open scoped WithZero

private theorem valuation_eq_one_iff_unitBounds {A Γ : Type*} [DivisionRing A]
    [LinearOrderedCommGroupWithZero Γ] (ν : Valuation A Γ) (a : Aˣ) :
    ν (a : A) = 1 ↔ ν (a : A) ≤ 1 ∧ ν (↑a⁻¹ : A) ≤ 1 := by
  have hmul : ν (a : A) * ν (↑a⁻¹ : A) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  constructor
  · intro h
    rw [h, one_mul] at hmul
    exact ⟨h.le, hmul.le⟩
  · rintro ⟨ha, ha'⟩
    apply le_antisymm ha
    calc
      1 = ν (a : A) * ν (↑a⁻¹ : A) := hmul.symm
      _ ≤ ν (a : A) * 1 := mul_le_mul_of_nonneg_left ha' zero_le
      _ = ν (a : A) := mul_one _

variable (k F B : Type u)
variable [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [DivisionRing B] [Algebra k B] [Algebra F B] [FiniteDimensional F B] [Algebra.IsCentral F B]

local instance : NontriviallyNormedField k := LocalGalois.localNormedField k
local instance : CompleteSpace k := LocalGalois.localNormedField_complete k
local instance : IsUltrametricDist k := LocalGalois.localNormedField_ultrametric k
local instance : NontriviallyNormedField F := LocalGalois.localNormedField F
local instance : CompleteSpace F := LocalGalois.localNormedField_complete F
local instance : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F

/-- Under split coordinates, both the opposite unit and the multiplier are integral units. -/
def splitIntegerUnits : Subgroup (splitInvolution k B).similitudes :=
  ((((integerRing F B).toSubmonoid.units.op).comap Units.opEquiv.toMonoidHom).prod
    (integerRing k k).toSubmonoid.units).comap (splitSimilitudeCoordinates k B).toMonoidHom

private theorem mem_divisionIntegerUnits (a : Bˣ) :
    a ∈ (integerRing F B).toSubmonoid.units ↔ localReducedNormIntValuation F B (a : B) = 1 := by
  rw [← Langlands.FormalGroup.LocalDivision.integerRing_eq_levelIntegerRing F B]
  change (localReducedNormValuation F B (a : B) ≤ 1 ∧
      localReducedNormValuation F B (↑a⁻¹ : B) ≤ 1) ↔
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
      (localReducedNormValuation F B (a : B)) = 1
  rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)]
  exact (valuation_eq_one_iff_unitBounds _ a).symm.trans
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).injective.eq_iff).symm

private theorem mem_scalarIntegerUnits (a : kˣ) :
    a ∈ (integerRing k k).toSubmonoid.units ↔
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (valuation k (a : k)) = 1 := by
  have hbound (x : k) : regularAbsoluteValue k k x ≤ 1 ↔ valuation k x ≤ 1 := by
    have h := regularAbsoluteValue_algebraMap k k x
    rw [Algebra.algebraMap_self_apply] at h
    rw [h]
    simpa only [norm_one, map_one] using LocalGalois.localNormedField_le k x 1
  change (regularAbsoluteValue k k (a : k) ≤ 1 ∧
      regularAbsoluteValue k k (↑a⁻¹ : k) ≤ 1) ↔ _
  rw [hbound, hbound, ← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k)]
  exact (valuation_eq_one_iff_unitBounds _ a).symm.trans
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k).injective.eq_iff).symm

/-- The local split valuation kernel is the subgroup of both integral unit coordinates. -/
theorem localSplitValuationCoordinates_ker :
    (localSplitValuationCoordinates k F B).ker = splitIntegerUnits k F B := by
  apply Subgroup.ext
  intro g
  unfold localSplitValuationCoordinates
  rw [mem_splitValuationKernel]
  change _ ↔
    (Units.opEquiv (splitSimilitudeCoordinates k B g).1).unop ∈
      (integerRing F B).toSubmonoid.units ∧
    (splitSimilitudeCoordinates k B g).2 ∈ (integerRing k k).toSubmonoid.units
  rw [mem_divisionIntegerUnits F B, mem_scalarIntegerUnits k]
  change _ ↔
    localReducedNormIntValuation F B (unop ((splitSimilitudeCoordinates k B g).1 : Bᵐᵒᵖ)) = 1 ∧
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
        (valuation k ((splitSimilitudeCoordinates k B g).2 : k)) = 1
  rw [splitSimilitudeCoordinates_fst, splitSimilitudeCoordinates_snd]
  rfl

end Langlands.FormalGroup.Harris
