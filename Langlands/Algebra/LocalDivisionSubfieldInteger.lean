import Langlands.Algebra.LocalDivisionIntegerLattice
import Langlands.Algebra.LocalDivisionResidueLift

/-! The original integer algebra and finite lattice of an actual embedded local subfield. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel

universe u uL

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  {L : Type uL} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

/-- The original integral scalar map, as an algebra structure on the actual integer ring. -/
@[instance_reducible]
def localDivisionSubfieldIntegerAlgebra :
    Algebra 𝒪[K] (localDivisionSubfieldValuation K D ι).integer :=
  (localDivisionSubfieldBaseIntegerMap K D ι).toAlgebra

/-- The original embedding maps integer elements linearly into the division integer lattice. -/
def localDivisionSubfieldIntegerToLattice :
    letI := localDivisionSubfieldIntegerAlgebra K D ι
    (localDivisionSubfieldValuation K D ι).integer →ₗ[𝒪[K]] localDivisionIntegerLattice K D := by
  letI := localDivisionSubfieldIntegerAlgebra K D ι
  exact
    { toFun := localDivisionSubfieldIntegerMap K D ι
      map_add' := fun x y => Subtype.ext (map_add ι x.val y.val)
      map_smul' := fun c x => Subtype.ext (by
        change ι (algebraMap K L (c : K) * x.val) = (c : K) • ι x.val
        rw [Algebra.smul_def, map_mul, ι.commutes]) }

@[simp]
theorem localDivisionSubfieldIntegerToLattice_coe
    (x : (localDivisionSubfieldValuation K D ι).integer) :
    (localDivisionSubfieldIntegerToLattice K D ι x : D) = ι (x : L) := rfl

theorem localDivisionSubfieldIntegerToLattice_injective :
    Function.Injective (localDivisionSubfieldIntegerToLattice K D ι) := fun _ _ h =>
  Subtype.ext (ι.injective (congrArg Subtype.val h))

/-- The actual subfield integer ring is finite over the original base integer ring. -/
theorem localDivisionSubfieldInteger_finite :
    letI := localDivisionSubfieldIntegerAlgebra K D ι
    Module.Finite 𝒪[K] (localDivisionSubfieldValuation K D ι).integer := by
  let := localDivisionSubfieldIntegerAlgebra K D ι
  let := localDivisionIntegerLattice_finite K D
  exact Module.Finite.of_injective (localDivisionSubfieldIntegerToLattice K D ι)
    (localDivisionSubfieldIntegerToLattice_injective K D ι)

end Langlands.CentralDivision
