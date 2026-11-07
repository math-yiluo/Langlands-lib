import Langlands.Representation.Exponents.RepresentedCuspidalityComparison
import Langlands.Representation.Aubert.General.RationalCompactRestrictionCuspidalProof
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionProof
import Langlands.Representation.Aubert.General.RationalPositiveCartanCoverProof
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement

/-! # Represented supercuspidality and compact norm-kernel restriction

Renard VI.2.1, (a) iff (c), with supercuspidality tested on every proper
actual rational parabolic. `HasCompactNormKernelRestriction` names condition
(c). The universal structural existence statements remain explicit
hypotheses; none of them is proved here.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RationalPointFamily

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : TopologicalSpace (rationalPoints G) := pointTopology

/-- Renard VI.2.1 (c): the restriction of `A` to the common norm kernel
`⁰G = Plancherel.rationalCommonNormKernel G` is compact, that is, every
coefficient of the restricted action against a smooth vector of its dual
has compact support in `⁰G`. -/
def HasCompactNormKernelRestriction (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) : Prop :=
  HasCompactSmoothDualCoefficients
    (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) A).representation

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Renard VI.2.1, (c) implies (a), for every proper actual parabolic:
compact coefficients on the common norm kernel imply represented
supercuspidality. -/
theorem isSupercuspidal_of_compactRestriction
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hRoot : RelativeRootSystemStatement.{u})
    (hG : IsConnectedReductive G)
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hA : HasCompactNormKernelRestriction A) :
    IsSupercuspidal A := by
  classical
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  obtain ⟨T, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have := hi.isSplitSubtorus.mono
  have hRoots := hRoot k G hG T i hi
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  have hU := isClosed_unipotent_of_isNonarchimedeanLocalField i ν
  have hcusp := rationalCompactRestrictionCuspidal k G hG T i hi ν hν hStandard
    hRoots hU A hA
  exact isSupercuspidal_of_isCuspidal i ν hPD hconj hG hi hν hRoots _ hU A hcusp

/-- Renard VI.2.1, (a) implies (c), for every proper actual parabolic:
represented supercuspidality implies compact coefficients on the common
norm kernel. -/
theorem compactRestriction_of_isSupercuspidal
    (hPD : ParabolicDynamicStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hRoot : RelativeRootSystemStatement.{u})
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hG : IsConnectedReductive G)
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (hA : IsSupercuspidal A) :
    HasCompactNormKernelRestriction A := by
  classical
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  obtain ⟨T, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have := hi.isSplitSubtorus.mono
  have hRoots := hRoot k G hG T i hi
  obtain ⟨D, x, Z, j, s, -, hrep, hsj, hchar, hvert, hprops, -, -, hcomp, -, -, hbasis⟩ :=
    hJoint k G hG T i hi ν hν
  have hcover := rationalPositiveCartanCover k G T i ν D x Z j s hchar hrep hsj hcomp
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  have hU := isClosed_unipotent_of_isNonarchimedeanLocalField i ν
  have hcusp := isCuspidal_of_all_represented_parabolics
    i ν hPD hStandard hG hi hν hRoots hU A hA
  exact rationalCuspidalCompactRestriction k G hG T i hi ν hν hStandard hRoots hU
    D x hvert hprops hbasis hcover A hcusp

/-- Renard VI.2.1, (a) iff (c), for every proper actual parabolic, with the
five universal structural existence statements kept explicit. -/
theorem isSupercuspidal_iff_compactRestriction
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hRoot : RelativeRootSystemStatement.{u})
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hG : IsConnectedReductive G)
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    IsSupercuspidal A ↔ HasCompactNormKernelRestriction A :=
  ⟨compactRestriction_of_isSupercuspidal hPD hStandard hRoot hJoint hG A,
    isSupercuspidal_of_compactRestriction hPD hconj hStandard hRoot hG A⟩

end Langlands.Aubert.General.RepresentedParabolic
