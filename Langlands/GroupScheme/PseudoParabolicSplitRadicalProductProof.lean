import Langlands.GroupScheme.PseudoParabolicSplitRadicalProductStatement
import Langlands.GroupScheme.SubgroupFunctor.FppfProductComposition
import Langlands.GroupScheme.Reductive.SplitRadicalQuotientAction
import Langlands.GroupScheme.Reductive.SplitRadicalWoundQuotientProof

/-! # The split-radical product description of pseudo-parabolics

The ordinary radical modulo the split radical is wound. The quotient-action
factorization and composition of fppf covers then give the product equality.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The dynamic parabolic has the same fppf-local product with the ordinary
and split ground-field unipotent radicals, on every relative scheme test. -/
theorem pseudoParabolicSplitRadicalProduct :
    PseudoParabolicSplitRadicalProductStatement.{u} := by
  intro k _ G _ _ _ U V j n hU hV χ T x
  let : Smooth U.X.hom := hU.smooth
  let : Smooth V.X.hom := hV.smooth
  let m : V ⟶ U := hV.inclusionInRadical hU
  have hm : m ≫ j = n := hV.inclusionInRadical_comp hU
  obtain ⟨Q, q, hsm, ha, hc, hq⟩ := hV.exists_quotient_inRadical hU
  let : Smooth Q.X.hom := hsm
  let : IsAffineHom Q.X.hom := ha
  let : ConnectedSpace Q.X.left := hc
  have hQ : HasConstantAffineLineMaps Q :=
    splitRadicalWoundQuotient k G U V j n hU hV m hm Q q hq
  have hlocal : SubgroupFunctor.FppfLocallyContainedInProduct
      (SubgroupFunctor.range j) (Dynamic.parabolic χ) (SubgroupFunctor.range n) := by
    intro W y hy
    exact fppfLocallyInProduct_parabolic_of_wound_quotient
      j n m hU.isClosedSubgroup hU.isNormal hV.isClosedSubgroup hV.isNormal
      hm q hq hQ χ W y hy
  exact hlocal.product_iff (hV.range_le_unipotentRadical hU) x

end Langlands.GroupScheme
