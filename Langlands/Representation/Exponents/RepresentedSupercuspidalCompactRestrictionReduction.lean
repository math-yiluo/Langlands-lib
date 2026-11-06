import Langlands.Representation.Aubert.General.RepresentedStandardCuspidality
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionProof
import Langlands.Representation.Aubert.General.RationalPositiveCartanCoverProof
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement

/-! # Structural reduction for represented supercuspidal compact restriction -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Aubert.General.RepresentedParabolic

open RationalPointFamily

/-- Four explicit universal structural inputs imply compact smooth-dual
coefficients on the actual common rational norm kernel for every smooth
representation whose proper represented Jacquet modules vanish. -/
def RepresentedSupercuspidalCompactRestrictionReductionStatement : Prop :=
  ParabolicDynamicStatement.{u} →
  StandardCocharacterStatement.{u} →
  RelativeRootSystemStatement.{u} →
  JointSpecialCompactBasisExistenceStatement.{u} →
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      (∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r)),
        ¬ IsIso p → Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj A)) →
      HasCompactSmoothDualCoefficients
        (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) A).representation

/-- Derived compact-restriction assembly. The structural existence premises
remain explicit, and no irreducibility or central-character premise is used. -/
theorem representedSupercuspidalCompactRestrictionReduction :
    RepresentedSupercuspidalCompactRestrictionReductionStatement.{u, v} := by
  intro hPD hStandard hRoot hJoint k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ A hA
  let : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  classical
  obtain ⟨T, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have := hi.isSplitSubtorus.mono
  have hRoots := hRoot k G hG T i hi
  obtain ⟨D, x, Z, j, s, -, hrep, hsj, hchar, -, hprops, -, -, hcomp, -, -, hbasis⟩ :=
    hJoint k G hG T i hi ν hν
  have hcover := rationalPositiveCartanCover k G T i ν D x Z j s hchar hrep hsj hcomp
  let hU := isClosed_unipotent_of_isNonarchimedeanLocalField i ν
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  have hcuspidal := isCuspidal_of_all_represented_parabolics
    i ν hPD hStandard hG hi hν hRoots hU A hA
  exact compactSmoothDualCoefficients_normKernel_of_jointDetection
    i ν hG hi hν hStandard hRoots hU (D.specialCompactSubgroup x)
    hprops.2.1.1 hbasis hcover
    (rationalCartanJointDetection i ν hG hi hν hRoots) A hcuspidal

end Langlands.Aubert.General.RepresentedParabolic
