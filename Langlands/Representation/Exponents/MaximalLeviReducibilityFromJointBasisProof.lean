import Langlands.Representation.Exponents.MaximalLeviReducibilityFromJointBasisStatement
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalReducibilityFromInputsProof
import Langlands.Representation.Exponents.MaximalLeviUnitarizableConstituentLeafReduction
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalInductionEndomorphismProof
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalInductionHomProof
import Langlands.Representation.Exponents.SupercuspidalCoefficientCompactSupportReduction
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelSupportGeometry
import Langlands.Representation.CompactCoefficient.UniformSupportFinitenessProof
import Langlands.Representation.Unitary.CompactCoefficientProof
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof

/-! # Proof of maximal-Levi reducibility from a joint compact basis -/

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme CuspidalSupport Plancherel Langlands.AlgebraicGeometry.PointTopology

private theorem normKernelFixedLevel_of_joint
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u}) :
    RationalNormKernelFixedLevelFinitenessStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
  have := rationalPoint_isTopologicalGroup k G
  intro _ _ _ ν hν hStd hRoots hU K hK
  let H := rationalCommonNormKernel G
  have : LocallyCompactSpace H := (isOpen_rationalCommonNormKernel G).locallyCompactSpace
  let : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  let haar : Measure H := Measure.haar
  exact CompactCoefficientClass.fixedStratum_finite_of_uniformSupport haar K hK
    (rationalNormKernelUniformSupport_of_joint hJoint k G hG T i hi ν hν hStd hRoots hU K hK)

private theorem supercuspidalUnitarizable_of_compactCoefficientSupport
    (hCompact : SupercuspidalUnitaryCoefficientCompactSupportStatement.{u, v}) :
    SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u, v} := by
  intro k _ _ _ _ _ H hH
  have := hH.isAffineHom
  have := hH.smooth
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : TopologicalSpace (rationalPoints H) := RationalPointFamily.pointTopology
  have : IsTopologicalGroup (rationalPoints H) := rationalPoint_isTopologicalGroup k H
  have : T2Space (rationalPoints H) := rationalPoint_t2Space k H
  intro _ _ ρ hirr hcusp hunitary
  obtain ⟨c⟩ := hunitary
  exact c.isUnitarizable_of_compact_coefficientNorm_of_nonarchimedean
    ρ.isSmooth hirr (hCompact k H hH ρ hirr hcusp c)

/-- The joint compact geometry gives the full conclusion of Renard VII.1.3
in the represented-parabolic interface. -/
theorem maximalLeviReducibilityFromJointBasis :
    MaximalLeviReducibilityFromJointBasisStatement.{u, v} := by
  intro hJoint
  have hDatum :=
    rationalPointsJacquetCartanDatum_of hJoint standardCocharacter standardParabolicOrder
  have hCompact :=
    supercuspidalUnitaryCoefficientCompactSupportStructuralReduction
      standardCocharacter relativeRootSystem hJoint
  exact maximalLeviSupercuspidalReducibilityFromInputs parabolicDynamic
    (rationalPointsIrreducibleAdmissible_of_jacquetCartanDatum hDatum)
    (rationalPointsIrreducibleAdmissible_of_jacquetCartanDatum hDatum)
    arbitraryParabolicQuotientCompact RationalPointFamily.rationalReductiveUnimodularity
    standardCocharacter parabolicRootPresentationExistence
    (supercuspidalUnitarizable_of_compactCoefficientSupport hCompact)
    maximalLeviSupercuspidalInductionEndomorphism maximalLeviSupercuspidalInductionHom
    (maximalLeviSupercuspidalUnitarizableConstituent_of_jointBasis_fixedLevel hJoint
      (normKernelFixedLevel_of_joint hJoint))

end Langlands.Aubert.General.RepresentedParabolic
