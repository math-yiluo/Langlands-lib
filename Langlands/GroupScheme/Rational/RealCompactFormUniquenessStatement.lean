import Langlands.GroupScheme.Rational.RealCompactPoints
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.Analysis.Complex.Basic

/-! # Statement: uniqueness of compact real semisimple forms -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Compact real semisimple groups with isomorphic complexifications are
isomorphic over the real field. -/
def RealCompactFormUniquenessStatement : Prop :=
  ∀ G₁ G₂ : GroupScheme (Spec (CommRingCat.of ℝ)),
    IsSemisimple G₁ → IsSemisimple G₂ →
    HasCompactRealPoints G₁ → HasCompactRealPoints G₂ →
    Nonempty ((GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G₁ ≅
      (GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G₂) →
    Nonempty (G₁ ≅ G₂)

end Langlands.GroupScheme
