import Langlands.Global.AdelicIwasawaReduction
import Langlands.Global.InfinitePlaceIwasawaProof
import Langlands.Global.FinitePlaceIwasawaProof
import Langlands.Global.IntegralIwasawaFamilyProof

/-! # Actual adelic parabolic Iwasawa existence: proof

`Langlands.Global.AdelicGroupPoints.parabolicIwasawaStatement` proves the published
`Langlands.Global.AdelicGroupPoints.ParabolicIwasawaStatement` (Getz–Hahn, Theorem 2.7.1
and equation (2.24), number-field case) by applying the reduction
`parabolicIwasawaStatement_of_archimedean_finite_integral` to the archimedean, finite-place
and integral-family existence theorems.
-/

universe u

namespace Langlands.Global.AdelicGroupPoints

/-- **Actual adelic parabolic Iwasawa existence.** For every number field `F`, connected
reductive `G` over `F` and actual parabolic inclusion `p : P ⟶ G`, some subgroup `K` of the
actual adelic point group `AdelicGroupPoints F G` is compact, maximal among all compact
subgroups, and satisfies `Set.range (map F P G p) * K = Set.univ`. -/
theorem parabolicIwasawaStatement : ParabolicIwasawaStatement.{u} :=
  parabolicIwasawaStatement_of_archimedean_finite_integral
    InfinitePlaceGroupPoints.parabolicIwasawaStatement
    FinitePlaceGroupPoints.parabolicIwasawaStatement
    IntegralIwasawaFamily.existenceStatement

end Langlands.Global.AdelicGroupPoints
