import Langlands.Representation.Geometric.RepresentedGeometricLemmaOrbitComparisonStatement
import Langlands.Representation.Geometric.RepresentedParabolicSupportJacquet
import Langlands.Representation.Geometric.RepresentedGeometricLemmaSupportGradedStatement
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement
import Langlands.Representation.Exponents.NormalizedTemperedSubrepresentation
import Langlands.Representation.Aubert.General.RestrictedLeviTopology
import Langlands.GroupScheme.Rational.ParabolicRootPresentationStatement
import Langlands.GroupScheme.Rational.SplitComponentProof

/-! # From local normalized orbit comparison to the full geometric lemma -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Actual quotient compactness, actual root presentation existence and the
local normalized comparison supply all grades of the original support filtration. -/
theorem representedGeometricLemmaSupportGraded_of_orbitComparison
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u})
    (hRoot : ParabolicRootPresentationExistenceStatement.{u})
    (hOrbit : RepresentedGeometricLemmaOrbitComparisonStatement.{u, v}) :
    RepresentedGeometricLemmaSupportGradedStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ m s D
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) := hCompact k G hG P p hp
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k L hlQ.isConnectedReductive).1
  obtain ⟨pres⟩ := hRoot k G hG Q L A q lQ a hq hlQ ha
  have hU : Jacquet.Localization.IsLimitOfCompactSubgroups (parabolicRadicalPoints q rQ) :=
    isLimitOfCompactSubgroups_subgroupOf _ _ (isClosed_pointImage q hq.isClosedSubgroup)
      (pointImage_radical_isLimitOfCompactSubgroups_of_presentation hG pres hrQ)
  intro i
  obtain ⟨e⟩ := hOrbit k G hG P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
    (s.representative i)⁻¹ (D i)
  simp only [inv_inv] at e
  exact ⟨leviJacquetSupportOrbitIso p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ hU s i ≪≫ e⟩

/-- The exact represented geometric lemma follows from its geometric prerequisite,
actual quotient compactness, root presentation existence and local orbit calculation. -/
theorem representedGeometricLemma_of_geometry_and_orbitComparison
    (hGeometry : RepresentedGeometricLemmaGeometryStatement.{u})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u})
    (hRoot : ParabolicRootPresentationExistenceStatement.{u})
    (hOrbit : RepresentedGeometricLemmaOrbitComparisonStatement.{u, v}) :
    RepresentedGeometricLemmaStatement.{u, v} :=
  representedGeometricLemma_of_geometry_and_supportGraded hGeometry
    (representedGeometricLemmaSupportGraded_of_orbitComparison hCompact hRoot hOrbit)

end Langlands.Aubert.General.RepresentedParabolic
