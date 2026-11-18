import Langlands.GroupScheme.Rational.RealCompactPoints
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.Analysis.Complex.Basic

/-! # Statement: a compact real form of every complex semisimple group -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every complex semisimple group scheme is the complexification of a real
semisimple group scheme with compact actual real points. -/
def RealCompactFormExistenceStatement : Prop :=
  ∀ G : GroupScheme (Spec (CommRingCat.of ℂ)), IsSemisimple G →
    ∃ H : GroupScheme (Spec (CommRingCat.of ℝ)), IsSemisimple H ∧
      HasCompactRealPoints H ∧
      Nonempty ((GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj H ≅ G)

end Langlands.GroupScheme
