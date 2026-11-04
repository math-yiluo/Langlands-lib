import Langlands.GroupScheme.CoalgebraUnipotence.ConilpotenceFromMatrix

universe u v

namespace Langlands.GroupScheme.CoalgebraUnipotence

theorem matrixUnipotenceConilpotence :
    MatrixUnipotenceConilpotenceStatement.{u, v} := by
  intro k _ B _ _
  exact ⟨isLocallyConilpotent_of_isMatrixUnipotent,
    isMatrixUnipotent_of_isLocallyConilpotent⟩

end Langlands.GroupScheme.CoalgebraUnipotence
