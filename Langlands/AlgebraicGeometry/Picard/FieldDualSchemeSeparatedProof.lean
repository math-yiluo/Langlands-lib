import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSeparatedStatement
import Langlands.AlgebraicGeometry.Picard.DualGroupScheme
import Langlands.AlgebraicGeometry.Picard.LocalComparisonProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs
import Langlands.AlgebraicGeometry.Modules.ExplicitPullbackTensorAssociativityProofs
import Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs
import Langlands.GroupScheme.FieldSeparatedProof

/-! # Separatedness of the chosen dual over a field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The chosen universal geometric Picard-zero parameter scheme over any field
has separated structural morphism. -/
theorem fieldDualSchemeSeparated : FieldDualSchemeSeparatedStatement.{u} := by
  intro k _ A hA
  let X := (relativeSpace A.X.hom).obj (dualScheme A hA)
  let P : X.Modules := (poincareFamily A hA).obj.carrier
  have hP : Langlands.CategoryTheory.TensorInvertible P :=
    (locallyFreeRankOneIffTensorInvertible X P).mpr (poincareFamily A hA).property
  obtain ⟨N, ⟨e⟩⟩ := hP
  have hN : IsLocallyFreeRankOne N :=
    (locallyFreeRankOneIffTensorInvertible X N).mp ⟨P, ⟨(β_ N P) ≪≫ e⟩⟩
  let M : LineBundle X := ⟨N, hN⟩
  let evaluation : tensorObj P M.obj ≅ structureSheaf X :=
    (localizedTensorIso X P N).symm ≪≫ e
  let G := dualCommGroupSchemeFromEvaluation A hA pullbackTensorComparisonIsIso
    M evaluation picardZeroPullback pullbackTensorComposition pullbackTensorUnitCoherence
    explicitPullbackTensorAssociativity tensorMonoidalLeftUnitorComparison pullbackTensorSymmetry
  exact Langlands.GroupScheme.fieldSeparated k G.toGrp

end Langlands.AbelianScheme
