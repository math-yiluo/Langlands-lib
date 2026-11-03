import Langlands.Galois.Local.SeparableUnramifiedFiniteArithmetic
import Langlands.Galois.Local.SeparableUnramifiedGaloisProof

noncomputable section

open IsLocalRing ValuativeRel

namespace Langlands.LocalGalois.Separable

universe u

section Maximality

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F
local instance : Finite (ResidueField (baseIntegers F)) := localResidue_finite F

theorem finiteUnramifiedMaximality : FiniteUnramifiedMaximality F := by
  intro E _
  exact (IntermediateField.le_iff_le (separableInertia F) E).trans
    ((inertia_le_fixingSubgroup_iff_residue_finrank F (SeparableClosure F) E).trans
      (arithmeticUnramified_iff_residue_finrank F E).symm)

end Maximality

/-- Finite arithmetic maximality and finite Galois exhaustion for the actual
separable inertia fixed field, in either characteristic. -/
theorem separableUnramified : SeparableUnramifiedStatement.{u} := by
  intro F _ _ _ _
  exact ⟨finiteUnramifiedMaximality F,
    finiteUnramifiedGaloisExhaustion_of_maximality F (finiteUnramifiedMaximality F)⟩

end Langlands.LocalGalois.Separable
