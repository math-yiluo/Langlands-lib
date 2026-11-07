import Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal
import Langlands.Representation.Exponents.RepresentedCuspidalRemainderSplittingStatement
import Langlands.Representation.CuspidalSupport.RationalWholeCuspidalComponents
import Langlands.Representation.CuspidalSupport.RationalNormKernelDecompositionStatement
import Langlands.Representation.Aubert.General.SharpCuspidalSeriesReduction

/-! # The represented cuspidal/remainder splitting from (KF)

Renard VI.3.5, two-summand form, for every proper actual parabolic. The
range and kernel of the norm-kernel compact projector form the splitting.
Condition (KF) and the five structural existence statements remain explicit
hypotheses; none of them is proved here.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RationalPointFamily

/-- The explicit six-input reduction to the exact represented splitting
statement. This proposition does not assert any of its inputs. -/
def RepresentedCuspidalRemainderSplittingReductionStatement : Prop :=
  CuspidalSupport.RationalNormKernelFixedLevelFinitenessStatement.{u, v} →
    ParabolicDynamicStatement.{u} →
    SmoothMaximalSplitTorusConjugacyStatement.{u} →
    StandardCocharacterStatement.{u} →
    RelativeRootSystemStatement.{u} →
    JointSpecialCompactBasisExistenceStatement.{u} →
    RepresentedCuspidalRemainderSplittingStatement.{u, v}

/-- Condition (KF) and the five structural existence statements imply the
represented objectwise cuspidal/remainder splitting. -/
theorem representedCuspidalRemainderSplitting_of_fixedLevelFiniteness
    (hKF : CuspidalSupport.RationalNormKernelFixedLevelFinitenessStatement.{u, v})
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hRoot : RelativeRootSystemStatement.{u})
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u}) :
    RepresentedCuspidalRemainderSplittingStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ A
  classical
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  obtain ⟨T, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have := hi.isSplitSubtorus.mono
  have hRoots := hRoot k G hG T i hi
  have hU := isClosed_unipotent_of_isNonarchimedeanLocalField i ν
  have hstrata := hKF k G hG T i hi ν hν hStandard hRoots hU
  have hmem := CuspidalSupport.rationalNormKernelCompactComponents_mem G hstrata A
  refine ⟨CuspidalSupport.rationalNormKernelCompactComponents G hstrata A,
    (CuspidalSupport.rationalNormKernelCompactCofan G hstrata A).inj, ?_, ?_,
    ⟨CuspidalSupport.rationalNormKernelCompactCofanIsColimit G hstrata A⟩⟩
  · exact isSupercuspidal_of_compactRestriction hPD hconj hStandard hRoot hG _
      (hmem true _ (SmoothRep.isSubquotient_self _))
  · intro D hD hDY hD'
    exact hmem false D hD hDY
      (compactRestriction_of_isSupercuspidal hPD hStandard hRoot hJoint hG D hD')

end Langlands.Aubert.General.RepresentedParabolic
