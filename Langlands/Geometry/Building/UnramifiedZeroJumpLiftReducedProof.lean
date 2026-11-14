import Langlands.Geometry.Building.UnramifiedAffineRootRestrictionReduction
import Langlands.Geometry.Building.RootJumpLiftNonMultipliable
import Langlands.GroupScheme.Rational.RankOneParabolicCovering
import Langlands.GroupScheme.Rational.KernelCentralizerComponentReductiveProof

/-! # Proof of the zero-value lift of root jumps for non-multipliable relative roots

This module proves `Langlands.Geometry.Building.UnramifiedZeroJumpLiftReducedStatement`, one of
the three inputs of `unramifiedAffineRootRestriction_of_zeroJumps`. It specializes
`exists_rootJump_lift_of_two_nsmul_not_mem` to `K = F^ur`, the valuation `x.val` of a point of
the upper apartment, and the value `r = 0`. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- **Zero-value root jumps lift, non-multipliable case.** If a relative root `α` of `(G, S)`
with `2α ∉ Φ(S)` has a filtration jump at value `0` for the restricted valuation `φ x`, then
some root `χ` of `(G_K, T_K)` restricting to `α` has a filtration jump at value `0` for `x`. -/
theorem unramifiedZeroJumpLiftReduced : UnramifiedZeroJumpLiftReducedStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have := mono_of_isMaximalSplitTorus hiS
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  intro hE D C _ fixed φ x _ α hα h2α hjump
  -- Rewrite `φ x` to the explicit restricted family before matching it against the lemma: the
  -- statement's nested proofs are auxiliary lemmas, and pointwise matching would unfold them.
  have hφx : φ x = torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
      hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) := by
    simp only [φ]
  rw [hφx] at hjump
  have hEbase : RelativeRoot.HasOppositeFactorPairs iS := fun a ha g hg _ =>
    RelativeRoot.exists_oppositeFactorPair_of_componentReductivity
      RelativeRoot.kernelCentralizerComponentReductive F G hG S iS hiS a ha.1 g hg
  have hfactor : CommGroupScheme.groupHom
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫
        (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS := by
    rw [← hf, Functor.map_comp]
    rfl
  exact exists_rootJump_lift_of_two_nsmul_not_mem (K := inertiaFixedField F) iS
    hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
    _ hfactor hEbase hα h2α 0 hjump

end Langlands.Geometry.Building
