import Langlands.Representation.Exponents.SupercuspidalCoefficientCompactSupportStatement
import Langlands.Representation.Aubert.General.RepresentedStandardCuspidality
import Langlands.Representation.Aubert.General.RationalCuspidalCoefficientCompactSupport
import Langlands.Representation.Aubert.General.RationalPositiveCartanCoverProof
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement

/-! # The structural inputs for represented-parabolic coefficient compactness -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Aubert.General.RepresentedParabolic

open RationalPointFamily

/-- The four displayed structural existence statements imply the unchanged
full-scope represented-parabolic coefficient compactness statement. -/
def SupercuspidalUnitaryCoefficientCompactSupportReductionStatement : Prop :=
  ParabolicDynamicStatement.{u} →
  StandardCocharacterStatement.{u} →
  RelativeRootSystemStatement.{u} →
  JointSpecialCompactBasisExistenceStatement.{u} →
  SupercuspidalUnitaryCoefficientCompactSupportStatement.{u, v}

/-- Conditional assembly of the exact represented-parabolic compactness target.
The four universal structural inputs remain explicit. -/
theorem supercuspidalUnitaryCoefficientCompactSupportReduction :
    SupercuspidalUnitaryCoefficientCompactSupportReductionStatement.{u, v} := by
  intro hPD hStandard hRoot hJoint k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ A _ hA c ℓ w
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
  exact compactUnitaryCoefficients_centerQuotient_of_isCuspidal
    i ν hG hi hν hStandard hRoots hU (D.specialCompactSubgroup x)
    hprops.2.1.1 hbasis hcover A hcuspidal c ℓ w

end Langlands.Aubert.General.RepresentedParabolic
