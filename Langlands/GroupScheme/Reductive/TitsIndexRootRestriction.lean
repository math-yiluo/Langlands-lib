import Langlands.GroupScheme.Reductive.TitsIndexRankOneOrbit
import Langlands.GroupScheme.Rational.RelativeRootMultiples
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Mathlib.Algebra.Module.Rat

/-! # Restriction of absolute weights and roots in an actual Tits index -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- Restrict an absolute weight to the maximal split torus, descending its
character from the separable closure to the ground field. -/
def rootRestrictionHom :
    characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
        d.pinning.torus) →+ characterLattice d.splitTorus :=
  (characterLattice.baseChangeEquiv (algebraBaseMap K (SeparableClosure K))
    d.splitTorus d.maximalSplit.1.1).symm.toAddMonoidHom.comp (TitsIndexStarProof.resK d)

@[simp] theorem rootRestrictionHom_root (a : d.pinning.rootIndex) :
    d.rootRestrictionHom (d.pinning.rootDatum.root a) = d.rootRestriction a := rfl

/-- Restriction of a reflected absolute root is the same integral reflection
formula applied to its restricted characters. -/
theorem rootRestriction_reflection (a b : d.pinning.rootIndex) :
    d.rootRestriction (d.pinning.rootDatum.reflectionPerm a b) =
      d.rootRestriction b -
        d.pinning.rootDatum.pairing b a • d.rootRestriction a := by
  rw [← d.rootRestrictionHom_root, d.pinning.rootDatum.root_reflectionPerm,
    d.pinning.rootDatum.reflection_apply_root, map_sub, map_zsmul,
    d.rootRestrictionHom_root, d.rootRestrictionHom_root]

/-- An actual absolute root cannot restrict to the third or a later positive
integral multiple of a distinguished simple root. -/
theorem rootRestriction_ne_nsmul_of_three_le (a : d.distinguishedVertices)
    (b : d.pinning.rootIndex) {n : ℕ} (hn : 3 ≤ n) :
    d.rootRestriction b ≠ n • d.rootRestriction a.val.val := by
  have ha : d.rootRestriction a.val.val ≠ 0 := a.property
  have hrel := TitsIndexStarProof.mem_relativeRoots_of_ne_zero d _ ha
  let := d.maximalSplit.isSplitSubtorus.mono
  have hR : HasRelativeRootSystem d.splitInclusion :=
    relativeRootSystem K G d.isSemisimple.isConnectedReductive
      d.splitTorus d.splitInclusion d.maximalSplit
  have : HasUniqueDiv (ℚ ⊗[ℤ] characterLattice d.splitTorus) :=
    HasUniqueDiv.of_module_rat _
  have : HasUniqueDiv (characterLattice d.splitTorus) :=
    d.maximalSplit.1.1.character_toRat_injective.hasUniqueDiv
      Langlands.LinearAlgebra.RationalSpan.toRat
  intro hb
  have hnonzero : d.rootRestriction b ≠ 0 := by
    rw [hb]
    exact (nsmul_eq_zero_iff_right (show n ≠ 0 by omega)).not.mpr ha
  exact hR.nsmul_not_mem_of_three_le hrel hn
    (hb ▸ TitsIndexStarProof.mem_relativeRoots_of_ne_zero d b hnonzero)

end Langlands.GroupScheme.TitsIndexData
