import Langlands.Algebra.LocalDivisionSubfieldCyclic

/-! Integral-unit lifts in actual full-residue embedded subfields. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel

universe u uL

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  {L : Type uL} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

/-- Every original integral unit has the residue of an integral unit in a full-residue subfield. -/
theorem exists_localDivisionSubfield_integerUnit
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (a : (localReducedNormValuation K D).integerˣ) :
    ∃ b : (localDivisionSubfieldValuation K D ι).integerˣ,
      localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _ b.val) =
        DivisionValuation.reduction _ a.val := by
  obtain ⟨z, hz⟩ := hsurj (DivisionValuation.reduction _ a.val)
  obtain ⟨x, hx⟩ := DivisionValuation.reduction_surjective
    (localDivisionSubfieldValuation K D ι) z
  have hred : localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _ x) =
      DivisionValuation.reduction _ a.val := by rw [hx, hz]
  have hne : DivisionValuation.reduction
      (localDivisionSubfieldValuation K D ι) x ≠ 0 := by
    intro h
    have ha : IsUnit (DivisionValuation.reduction (localReducedNormValuation K D) a.val) :=
      a.isUnit.map (DivisionValuation.reduction _)
    apply ha.ne_zero
    rw [← hred, h, map_zero]
  have hu := (DivisionValuation.isUnit_iff_value_eq_one _ x).mpr
    ((DivisionValuation.reduction_ne_zero_iff _ x).mp hne)
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  exact hred

/-- A chosen actual integral-unit lift with the prescribed residue. -/
def localDivisionSubfieldIntegerUnitLift
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (a : (localReducedNormValuation K D).integerˣ) :
    (localDivisionSubfieldValuation K D ι).integerˣ :=
  Classical.choose (exists_localDivisionSubfield_integerUnit K D ι hsurj a)

theorem localDivisionSubfieldIntegerUnitLift_spec
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (a : (localReducedNormValuation K D).integerˣ) :
    localDivisionSubfieldResidueMap K D ι
        (DivisionValuation.reduction _ (localDivisionSubfieldIntegerUnitLift K D ι hsurj a).val) =
      DivisionValuation.reduction _ a.val :=
  Classical.choose_spec (exists_localDivisionSubfield_integerUnit K D ι hsurj a)

end Langlands.CentralDivision
