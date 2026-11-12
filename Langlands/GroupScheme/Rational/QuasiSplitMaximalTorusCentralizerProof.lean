import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerReduction
import Langlands.GroupScheme.Rational.QuasiSplitCentralizerTorus
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Maximal tori containing a maximal split torus in quasi-split groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every quasi-split field group has some maximal split torus whose whole-group
centralizer is represented by a closed torus. -/
theorem quasiSplitTorusCentralizerExistence :
    QuasiSplitTorusCentralizerExistenceStatement.{u} := by
  intro k _ G hG
  obtain ⟨A, a, ha, C, c, hc, hcl, hC⟩ :=
    hG.exists_maximalSplitTorus_with_torusCentralizer dynamicCentralizerReductive
      parabolicDynamic
  exact ⟨A, a, C, c, ha, hc, hcl, hC⟩

/-- In a quasi-split connected reductive group, any maximal torus containing an
ambient maximal split torus represents its whole-group centralizer. -/
theorem quasiSplitMaximalTorusCentralizer :
    QuasiSplitMaximalTorusCentralizerStatement.{u} :=
  quasiSplitMaximalTorusCentralizer_of_exists_torusCentralizer
    quasiSplitTorusCentralizerExistence maximalSplitTorusConjugacy

end Langlands.GroupScheme
