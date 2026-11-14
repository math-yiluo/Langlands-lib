import Langlands.GroupScheme.Rational.SimpleRootSplitCentralImageStatement
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Rational.CentralRootRestriction

/-! # Integral simple-root annihilators and split components: proof -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Simple-root annihilation detects precisely the integral cocharacters
coming from the actual split component along any compatible lift. -/
theorem simpleRootSplitCentralImage : SimpleRootSplitCentralImageStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  have := hi.isSplitSubtorus.mono
  intro ν hν A a ha f hf
  apply le_antisymm
  · rw [ha.range_cocharacterMapInt_eq_centralCocharacters f hf]
    intro eta heta
    apply rootAnnihilatorCentrality k G T hi.1.1 i eta
    let e : characterLattice T →+ ℤ :=
      ((latticePairing T).flip eta).toAddMonoidHom
    have hsimple : simpleRelativeRoots i ν ⊆ e.ker := by
      intro α hα
      exact (RealTorusSpace.mem_rootAnnihilatorInt _ _).mp heta α hα
    have hall := relativeRoots_subset_addSubgroupClosure_simpleRelativeRoots
      i ν hν (relativeRootNegation k G hG T i hi)
    intro α hα
    exact ((AddSubgroup.closure_le e.ker).mpr hsimple) (hall hα)
  · rintro _ ⟨eta, rfl⟩
    apply (RealTorusSpace.mem_rootAnnihilatorInt _ _).mpr
    intro α hα
    have hc : IsCentral (CommGroupScheme.groupHom f ≫ i) := by
      rw [hf]
      exact ha.1.2
    have hrestrict := root_restrict_eq_zero_of_isCentral i f ha.1.1.1 hc hα.1.1
    change gmEndEquiv k ((eta ≫ f) ≫ α) = 0
    rw [Category.assoc, hrestrict, Limits.comp_zero, map_zero]

end Langlands.GroupScheme
