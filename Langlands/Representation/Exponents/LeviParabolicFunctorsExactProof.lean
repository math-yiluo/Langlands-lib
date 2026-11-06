import Langlands.Representation.Exponents.LeviParabolicFunctorsExactStatement
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Plancherel.RationalModerateGrowthUniformization

/-! # Proof of exactness of normalized parabolic induction and restriction

Renard 2026, VI.1.2 Proposition, exactness part, for represented parabolics.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Renard VI.1.2 Proposition, exactness part: the normalized functors of a represented
parabolic send short exact sequences to short exact sequences. -/
theorem leviParabolicFunctorsExact : LeviParabolicFunctorsExactStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  have hdec := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  have hU := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  refine ⟨fun f g hfg => ?_, fun f g hfg => ?_⟩
  · have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    have := hG.smooth
    have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
    exact normalizedInductionFunctor_map_isShortExact
      (Plancherel.rationalPoint_compactOpenCofinal k G) hdec hU
      (isClosed_pointImage p hp.isClosedSubgroup)
      (continuous_projection_pointImage p l r hp hl hr hmul)
      ((SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm).map f)
      ((SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm).map g) hfg
  · exact jacquetFunctor_map_isShortExact hdec hU
      (isLimitOfCompactSubgroups_pointImage_radical p r hp.isClosedSubgroup hr.1) f g hfg

end Langlands.Aubert.General.RepresentedParabolic
