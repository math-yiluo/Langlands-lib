import Langlands.GroupScheme.PseudoParabolicSplitNormalProduct
import Langlands.GroupScheme.PseudoParabolicSplitRadicalContainmentStatement
import Langlands.GroupScheme.PseudoParabolicSplitRadicalProductProof

/-! # Split radical containment for pseudo-parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Both the contracting subgroup and the ambient split radical lie in
the supplied split radical of the pseudo-parabolic, on every relative test. -/
theorem pseudoParabolicSplitRadicalContainment :
    PseudoParabolicSplitRadicalContainmentStatement.{u} := by
  intro k _ G _ _ _ R r hr χ P i hP V W n m hn hm
  have hPs : (Dynamic.parabolic χ).IsFppfProduct (SubgroupFunctor.range n) i :=
    { isClosedSubgroup := hP.isClosedSubgroup
      mem_range_iff := fun T x =>
        (hP.mem_range_iff T x).trans
          (pseudoParabolicSplitRadicalProduct k G R V r n hr hn χ T x) }
  exact PseudoParabolicSplitNormalProduct.containment χ n i hPs hn m hm

end Langlands.GroupScheme
