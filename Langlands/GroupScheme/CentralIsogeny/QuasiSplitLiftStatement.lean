import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Statement: quasi-splitness lifts along central isogenies -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Quasi-splitness lifts along central isogenies.** If `π : G ⟶ A` is a central isogeny
of group schemes over a field `K`, `G` is connected reductive and `A` is quasi-split, then
`G` is quasi-split. -/
def CentralIsogenyQuasiSplitLiftStatement : Prop :=
  ∀ (K : Type u) [Field K] (G A : GroupScheme (Spec (CommRingCat.of K))) (π : G ⟶ A),
    IsCentralIsogeny π → IsConnectedReductive G → IsQuasiSplit A → IsQuasiSplit G

end Langlands.GroupScheme
