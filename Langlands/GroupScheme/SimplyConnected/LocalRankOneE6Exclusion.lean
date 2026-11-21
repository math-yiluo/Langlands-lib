import Langlands.GroupScheme.SimplyConnected.LocalRankOneE7Exclusion
import Langlands.GroupScheme.SimplyConnected.TypeE6KernelEndpoint
import Langlands.GroupScheme.SimplyConnected.TypeE6KernelTripleWeight
import Langlands.GroupScheme.SimplyConnected.NormOneTitsNormalization
import Langlands.GroupScheme.SimplyConnected.TitsObstructionRootVanishing
import Langlands.GroupScheme.Reductive.SplitLeviTitsComparison
import Langlands.Algebra.DivisionBrauerClass

/-! # Exclusion of the inner E6 branch marking -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Brauer Langlands.CentralSimple

namespace Langlands.GroupScheme.TitsIndexData

private theorem cartan_A_finCongr {n m : ℕ} (h : n = m) (a b : Fin n) :
    CartanMatrix.A n a b = CartanMatrix.A m (finCongr h a) (finCongr h b) := by
  subst m
  rfl

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inner E6 branch marking is impossible for the actual index of a
simply connected group. -/
theorem not_hasRankOneE6BranchIndex (hsc : IsSimplyConnected G) :
    ¬ d.HasRankOneE6BranchIndex := by
  rintro ⟨⟨q, hq⟩, hstar⟩
  let p := d.anisotropicKernelIndex
  let hP := p.isSimplyConnected hsc
  let lam : d.pinning.starFixedWeights := ⟨d.e6TripleFirstWeight hsc q,
    (d.pinning.mem_starFixedWeights _).mpr (d.e6TripleFirstWeight_isStarFixed hsc q hstar)⟩
  have hlam : d.pinning.titsObstruction hsc lam = 0 :=
    d.pinning.titsObstruction_eq_zero_of_mem_rootSpan_unconditional hsc lam
      (d.e6TripleFirstWeight_mem_rootSpan hsc q hq.1)
  obtain ⟨D, _, _, _, _, hdegree, ⟨eModel⟩⟩ :=
    d.anisotropicKernel_divisionModel_of_E6_branch_mark q hsc hq hstar
  let A := divisionAlgebra k D
  let model : p.kernel ≅ CentralSimpleUnits.normOne k A := eModel
  have hdeg : reducedDegree k A = 6 := hdegree
  have hsize : 2 ≤ reducedDegree k A := by rw [hdeg]; decide
  let inner := CentralSimpleUnits.normOneInnerStar p.index.pinning A model
    (separableClosureChart k A)
  let μ := p.comparison.e6BranchFirstWeight q hq hP
  let mu : p.index.pinning.starFixedWeights :=
    p.index.pinning.fixedWeightOfInner hP inner μ
  have hrestrict :
      p.leviComparison.starFixedRestriction
          (p.index.pinning.corootSpan_eq_top_of_simplyConnected hP) lam = (3 : ℤ) • mu := by
    apply Subtype.ext
    change p.leviComparison.weightRestriction (d.e6TripleFirstWeight hsc q) = (3 : ℤ) • μ
    rw [p.leviComparison_weightRestriction, d.weightRestriction_e6TripleFirstWeight hsc q hq]
    exact congrArg ((3 : ℤ) • ·) (p.comparison.e6BranchFirstWeight_eq_firstWeight q hq hP).symm
  have hzero : (3 : ℤ) • p.index.pinning.innerTitsObstruction hP inner μ = 0 := by
    rw [p.index.pinning.innerTitsObstruction_apply, ← map_zsmul, ← hrestrict]
    exact (p.titsObstruction_eq hsc lam).symm.trans hlam
  obtain ⟨e, he, _, hleft, hright⟩ :=
    CentralSimpleUnits.normOneAbsoluteTitsNormalization p.index.pinning A model hsize
  let e5 : p.index.Vertex ≃ Fin 5 := e.trans (finCongr (by omega))
  have he5 (a b : p.index.Vertex) :
      p.index.cartan a b = CartanMatrix.A 5 (e5 a) (e5 b) := by
    change p.index.pinning.toSplitPinning.rootDatum.pairing a.val b.val = _
    exact (he a b).trans (cartan_A_finCongr (by omega) (e a) (e b))
  have hfirst : e5.symm 0 = e.symm ⟨0, by omega⟩ := by
    apply congrArg e.symm
    rfl
  have hlast : e5.symm 4 = e.symm ⟨reducedDegree k A - 2, by omega⟩ := by
    apply congrArg e.symm
    apply Fin.ext
    change 4 = reducedDegree k A - 2
    omega
  have hnonzero := three_zsmul_classOf_divisionAlgebra_ne_zero k D hdegree
  rcases p.comparison.e6BranchFirstWeight_eq_endpoint q hq hP e5 he5 with hμ | hμ
  · have hvalue : p.index.pinning.innerTitsObstruction hP inner μ = classOf A := by
      change p.index.pinning.innerTitsObstruction hP inner
        (p.comparison.e6BranchFirstWeight q hq hP) = _
      rw [hμ, hfirst]
      exact hleft
    rw [hvalue] at hzero
    exact hnonzero hzero
  · have hvalue : p.index.pinning.innerTitsObstruction hP inner μ = -classOf A := by
      change p.index.pinning.innerTitsObstruction hP inner
        (p.comparison.e6BranchFirstWeight q hq hP) = _
      rw [hμ, hlast]
      exact hright
    rw [hvalue, smul_neg, neg_eq_zero] at hzero
    exact hnonzero hzero

end Langlands.GroupScheme.TitsIndexData
