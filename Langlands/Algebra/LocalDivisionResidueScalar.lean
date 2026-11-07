import Langlands.Algebra.LocalDivisionResidue
import Mathlib.FieldTheory.Finite.Basic

/-! The original base residue field and residue generators in a local central division algebra. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance : Field (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueField K D

/-- The original central scalar inclusion restricted to the actual integer subrings. -/
def localDivisionIntegerMap : 𝒪[K] →+* (localReducedNormValuation K D).integer where
  toFun a := ⟨algebraMap K D a.val, by
    change localReducedNormValuation K D (algebraMap K D a.val) ≤ 1
    rw [localReducedNormValuation_algebraMap]
    exact pow_le_one₀ zero_le a.prop⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a.val b.val)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)

@[simp]
theorem localDivisionIntegerMap_coe (a : 𝒪[K]) :
    (localDivisionIntegerMap K D a : D) = algebraMap K D (a : K) := rfl

/-- The residue reduction of an original integral scalar. -/
def localDivisionBaseReduction :
    𝒪[K] →+* DivisionValuation.Residue (localReducedNormValuation K D) :=
  (DivisionValuation.reduction (localReducedNormValuation K D)).comp
    (localDivisionIntegerMap K D)

/-- The scalar reduction has the exact original base-field strict-value kernel. -/
theorem localDivisionBaseReduction_eq_zero_iff (a : 𝒪[K]) :
    localDivisionBaseReduction K D a = 0 ↔ valuation K (a : K) < 1 := by
  change DivisionValuation.reduction _ (localDivisionIntegerMap K D a) = 0 ↔ _
  rw [DivisionValuation.reduction_eq_zero_iff, localDivisionIntegerMap_coe,
    localReducedNormValuation_algebraMap]
  exact pow_lt_one_iff_of_nonneg zero_le (CentralSimple.reducedDegree_pos K D).ne'

instance localDivisionBaseReduction_isLocalHom : IsLocalHom (localDivisionBaseReduction K D) where
  map_nonunit a ha := by
    apply (DivisionValuation.isUnit_iff_value_eq_one (valuation K) a).mpr
    have hn : localDivisionBaseReduction K D a ≠ 0 := isUnit_iff_ne_zero.mp ha
    have hle : 1 ≤ valuation K (a : K) := by
      exact not_lt.mp (fun h => hn ((localDivisionBaseReduction_eq_zero_iff K D a).mpr h))
    exact le_antisymm a.prop hle

/-- The actual base residue field embeds in the actual division-algebra residue field. -/
def localDivisionResidueScalarMap :
    𝓀[K] →+* DivisionValuation.Residue (localReducedNormValuation K D) :=
  IsLocalRing.ResidueField.lift (localDivisionBaseReduction K D)

@[simp]
theorem localDivisionResidueScalarMap_residue (a : 𝒪[K]) :
    localDivisionResidueScalarMap K D (IsLocalRing.residue 𝒪[K] a) =
      DivisionValuation.reduction (localReducedNormValuation K D) (localDivisionIntegerMap K D a) :=
  rfl

theorem localDivisionResidueScalarMap_injective :
    Function.Injective (localDivisionResidueScalarMap K D) :=
  (localDivisionResidueScalarMap K D).injective

/-- The scalar action on the actual residue field induced from the original integral scalars. -/
@[instance_reducible]
def localDivisionResidueAlgebra :
    Algebra 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  (localDivisionResidueScalarMap K D).toAlgebra

/-- This actual residue-field extension is finite-dimensional. -/
theorem localDivisionResidue_finiteDimensional :
    letI := localDivisionResidueAlgebra K D
    FiniteDimensional 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) := by
  let := localDivisionResidueAlgebra K D
  infer_instance

/-- An original integral unit lifts a multiplicative generator of the actual residue field. -/
theorem exists_localDivisionResidue_unit_generator :
    ∃ a : (localReducedNormValuation K D).integerˣ,
      ∀ z : (DivisionValuation.Residue (localReducedNormValuation K D))ˣ,
        ∃ n : ℕ, z = Units.map
          (DivisionValuation.reduction (localReducedNormValuation K D)).toMonoidHom (a ^ n) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
    (α := (DivisionValuation.Residue (localReducedNormValuation K D))ˣ)
  obtain ⟨a, ha⟩ := DivisionValuation.reduction_units_surjective
    (localReducedNormValuation K D) g
  refine ⟨a, fun z => ?_⟩
  have hz : z ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.mpr (hg z)
  obtain ⟨n, hn⟩ := hz
  refine ⟨n, ?_⟩
  rw [map_pow, ha]
  exact hn.symm

/-- Every actual residue element is zero or the reduction of a power of one integral unit. -/
theorem exists_localDivisionResidue_generator :
    ∃ a : (localReducedNormValuation K D).integerˣ,
      ∀ z : DivisionValuation.Residue (localReducedNormValuation K D),
        z = 0 ∨ ∃ n : ℕ,
          z = DivisionValuation.reduction (localReducedNormValuation K D) (a.val ^ n) := by
  obtain ⟨a, ha⟩ := exists_localDivisionResidue_unit_generator K D
  refine ⟨a, fun z => ?_⟩
  by_cases hz : z = 0
  · exact Or.inl hz
  · obtain ⟨n, hn⟩ := ha (Units.mk0 z hz)
    refine Or.inr ⟨n, ?_⟩
    exact congrArg Units.val hn

end Langlands.CentralDivision
