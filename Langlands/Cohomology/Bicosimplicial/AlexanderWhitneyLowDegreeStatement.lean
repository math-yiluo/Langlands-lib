import Langlands.Cohomology.Bicosimplicial.AlexanderWhitney
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Low-degree cohomology of the Alexander–Whitney map

This proposition restricts the cosimplicial Eilenberg–Zilber comparison to degrees
zero through two. See Grunenfelder and Mastnak, *Cohomology of abelian matched pairs
and the Kac sequence*, J. Algebra 276 (2004), Appendix A.2, Theorem A.3, and Appendix A.3
for the cohomology isomorphism induced by the explicit cochain map.
-/

open CategoryTheory

universe u v

namespace Langlands.Cohomology.Bicosimplicial

/-- The Alexander–Whitney comparison from the signed total complex to the diagonal
alternating-coface complex induces an isomorphism on cohomology in degrees `0`, `1`, and `2`. -/
def AlexanderWhitneyLowDegreeQuasiIsoStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (F : SimplexCategory × SimplexCategory ⥤ ModuleCat.{v} R) (n : ℕ),
    n ≤ 2 → QuasiIsoAt (alexanderWhitney F) n

end Langlands.Cohomology.Bicosimplicial
