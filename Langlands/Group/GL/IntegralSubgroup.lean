import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Integral matrix subgroups over topological rings

The subgroup requires entries of both the matrix and its inverse to lie in the
specified subring. All finite index types are allowed, including the empty type.
-/

namespace Langlands.GeneralLinearGroup

universe u v

variable {R : Type u} [CommRing R]
variable (ι : Type v) [Fintype ι] [DecidableEq ι] (O : Subring R)

/-- Matrix units whose forward and inverse matrices have entries in `O`. -/
def integralSubgroup : Subgroup (Matrix.GeneralLinearGroup ι R) :=
  (O.matrix (n := ι)).toSubmonoid.units

@[simp]
theorem mem_integralSubgroup (g : Matrix.GeneralLinearGroup ι R) :
    g ∈ integralSubgroup ι O ↔
      (∀ i j, g i j ∈ O) ∧ (∀ i j, g⁻¹ i j ∈ O) :=
  Iff.rfl

@[simp]
theorem integralSubgroup_of_isEmpty [IsEmpty ι] :
    integralSubgroup ι O = ⊤ := by
  ext g
  simp [mem_integralSubgroup]

variable [TopologicalSpace R]

/-- Openness follows from openness of the entries of both inverse matrices. -/
theorem isOpen_integralSubgroup (hO : IsOpen (O : Set R)) :
    IsOpen (integralSubgroup ι O : Set (Matrix.GeneralLinearGroup ι R)) :=
  Submonoid.isOpen_units hO.matrix

/-- The actual integral subgroup, packaged with its inherited open topology. -/
def integralOpenSubgroup (hO : IsOpen (O : Set R)) :
    OpenSubgroup (Matrix.GeneralLinearGroup ι R) where
  toSubgroup := integralSubgroup ι O
  isOpen' := isOpen_integralSubgroup ι O hO

@[simp]
theorem mem_integralOpenSubgroup (hO : IsOpen (O : Set R))
    (g : Matrix.GeneralLinearGroup ι R) :
    g ∈ integralOpenSubgroup ι O hO ↔
      (∀ i j, g i j ∈ O) ∧ (∀ i j, g⁻¹ i j ∈ O) :=
  Iff.rfl

variable [T2Space R] [IsTopologicalRing R]

/-- Compactness uses the closed inverse-pair equations in two compact matrix sets. -/
theorem isCompact_integralSubgroup (hO : IsCompact (O : Set R)) :
    IsCompact (integralSubgroup ι O : Set (Matrix.GeneralLinearGroup ι R)) :=
  Submonoid.units_isCompact hO.matrix

theorem isCompact_integralOpenSubgroup
    (hOpen : IsOpen (O : Set R)) (hCompact : IsCompact (O : Set R)) :
    IsCompact (integralOpenSubgroup ι O hOpen :
      Set (Matrix.GeneralLinearGroup ι R)) :=
  isCompact_integralSubgroup ι O hCompact

end Langlands.GeneralLinearGroup
