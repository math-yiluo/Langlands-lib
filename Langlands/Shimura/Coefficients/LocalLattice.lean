import Langlands.Shimura.Coefficients.Lattice
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Valued.ValuationTopology

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open Set Module
open scoped TensorProduct WithZero

section Coordinates

variable (R : Type u) [CommRing R] [IsDomain R]
variable {K : Type v} [Field K] [Algebra R K] [Module.IsTorsionFree R K]
variable {V : Type w} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable {ι : Type*} [Finite ι] (b : Basis ι K V)

/-- The integral coordinate lattice for a finite basis. -/
def basisLattice : Submodule R V := Submodule.span R (Set.range b)

instance basisLattice_isLattice : Submodule.IsLattice K (basisLattice R b) where
  fg := Submodule.fg_span (Set.finite_range b)
  span_eq_top := by
    rw [basisLattice, Submodule.span_span_of_tower, b.span_eq]

omit [Finite ι] in
theorem mem_basisLattice (x : V) :
    x ∈ basisLattice R b ↔ ∀ i, b.repr x i ∈ Set.range (algebraMap R K) :=
  b.mem_span_iff_repr_mem R x

variable [TopologicalSpace K] [IsTopologicalRing K]
variable [TopologicalSpace V] [IsModuleTopology K V]

/-- Open integral coordinates give an open lattice in the module topology. -/
theorem basisLattice_isOpen (hR : IsOpen (Set.range (algebraMap R K))) :
    IsOpen (basisLattice R b : Set V) := by
  have heq : (basisLattice R b : Set V) =
      ⋂ i, (fun x : V => b.repr x i) ⁻¹' Set.range (algebraMap R K) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, mem_basisLattice]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  exact hR.preimage (IsModuleTopology.continuous_of_linearMap (b.coord i))

end Coordinates

section Coefficients

open Langlands.Global

variable (L : Type u) [Field L] [NumberField L] (l : FinitePlace L)
variable (W : Type w) [AddCommGroup W] [Module L W] [Module.Finite L W]

/-- The canonical finite-dimensional module topology on the completed coefficient space. -/
abbrev coefficientTopology : TopologicalSpace (FiniteCompletion L l ⊗[L] W) :=
  moduleTopology (FiniteCompletion L l) (FiniteCompletion L l ⊗[L] W)

/-- An actual full integral lattice, obtained from a finite basis of the completed space. -/
def coefficientLattice : Submodule (CoefficientIntegers l) (FiniteCompletion L l ⊗[L] W) :=
  basisLattice (CoefficientIntegers l) (Module.finBasis (FiniteCompletion L l)
    (FiniteCompletion L l ⊗[L] W))

instance coefficientLattice_isLattice :
    Submodule.IsLattice (FiniteCompletion L l) (coefficientLattice L l W) := by
  unfold coefficientLattice
  infer_instance

/-- This explicitly constructed coordinate lattice is open. -/
theorem coefficientLattice_isOpen :
    letI := coefficientTopology L l W
    IsOpen (coefficientLattice L l W : Set (FiniteCompletion L l ⊗[L] W)) := by
  let _ := coefficientTopology L l W
  apply basisLattice_isOpen
  have heq : Set.range (algebraMap (CoefficientIntegers l) (FiniteCompletion L l)) =
      ((Valued.v : Valuation (FiniteCompletion L l) ℤᵐ⁰).valuationSubring : Set (FiniteCompletion L l)) := by
    exact Subtype.range_coe_subtype
  rw [heq]
  exact Valued.isOpen_valuationSubring _

end Coefficients

end Langlands.Shimura.Coefficients
