import Langlands.GroupScheme.Rational.SplitUnipotentStableCenter
import Langlands.GroupScheme.Rational.SplitCommutativeVector
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitStatement

/-! # Central stable vector subgroups from perfect-field splitness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeRoot

/-- Splitness of smooth connected unipotent groups over perfect fields gives central stable
vector subgroups of split unipotent groups over every field. -/
theorem splitUnipotentStableVectorSubgroup_of_perfectFieldUnipotentSplit
    (hP : PerfectFieldUnipotentSplitStatement.{u}) :
    SplitUnipotentStableVectorSubgroupStatement.{u} := by
  intro k _ U hs ha hc hU hS hnt H _ hH a
  have := hs
  have := ha
  have : ConnectedSpace U.X.left := hc
  have hk : Infinite k ∨ RationalDensity.UnipotentSplitOver k := by
    rcases finite_or_infinite k with hfin | hinf
    · have := hfin
      exact Or.inr fun Z _ _ hZc hZu => hP k Z hZc hZu
    · exact Or.inl hinf
  exact RationalDensity.splitUnipotentStableVectorSubgroup_of_isVectorGroup
    (fun W _ _ _ _ hW hq => isVectorGroup_of_isSplitUnipotent_of_exponent W hW hq)
    hk U hU hS hnt H a

end Langlands.GroupScheme.RelativeRoot
