import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Reductive.Semisimple

/-! # A common semisimple central refinement of two central isogenies -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Two central isogenies between semisimple field groups admit a common semisimple
source mapping centrally isogenously to both sources over the same target. -/
def CentralIsogenyCommonSemisimpleRefinement : Prop :=
  ∀ (k : Type u) [Field k]
    (C H G : GroupScheme (Spec (CommRingCat.of k))) (π : C ⟶ G) (q : H ⟶ G),
    IsSemisimple C → IsSemisimple H → IsSemisimple G →
      IsCentralIsogeny π → IsCentralIsogeny q →
        ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (p : D ⟶ C) (r : D ⟶ H),
          IsSemisimple D ∧ IsCentralIsogeny p ∧ IsCentralIsogeny r ∧ p ≫ π = r ≫ q

end Langlands.GroupScheme
