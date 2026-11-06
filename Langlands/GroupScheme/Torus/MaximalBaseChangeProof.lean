import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement
import Langlands.GroupScheme.Torus.MaximalBaseChangeReflection
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.Torus.NoTorusBaseChangeReduction
import Langlands.GroupScheme.Torus.CentralizerSmoothProof
import Langlands.GroupScheme.Torus.CentralMaximalQuotientProof
import Langlands.GroupScheme.Torus.NoTorusUnipotent
import Langlands.GroupScheme.NormalSubgroupQuotientProof

/-! # Maximality of tori under field extension (Milne, Theorem 17.82) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne, Theorem 17.82: a closed torus in a smooth affine group is maximal exactly when its
base change to a field extension is maximal. -/
theorem maximalTorusBaseChange : MaximalTorusBaseChangeStatement.{u} := by
  intro k K _ _ _ G _ _ T i _ hi
  exact ⟨maximalTorusBaseChangeForwardReduction torusCentralizerSmooth
      (centralMaximalTorusBaseChangeReduction normalSubgroupQuotient
        centralMaximalTorusQuotientStatement (noTorusBaseChangeReduction noTorusUnipotent))
      k K G T i,
    IsMaximalTorus.of_baseChange hi⟩

end Langlands.GroupScheme
