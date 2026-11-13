import Langlands.Representation.Exponents.MaximalLeviUnitarizableConstituentReduction
import Langlands.Representation.Exponents.CasselmanSufficiencyReduction
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalGeometricReduction
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalLengthTwoReduction
import Langlands.Representation.Exponents.RepresentedCuspidalRemainderSplittingReduction
import Langlands.Representation.Aubert.General.RationalJacquetCartanDatum
import Langlands.Representation.Aubert.General.IrreducibleAdmissibleOfDatum
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof
import Langlands.GroupScheme.Rational.MaximalLeviContainmentProof
import Langlands.GroupScheme.Rational.MaximalLeviConeComplementProof
import Langlands.GroupScheme.Rational.ParabolicNormalizerProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # The unitarizable-constituent step of Renard VII.1.3 from two open inputs

Renard 2026, VII.1.3 (PDF pp.230–232). The published nine-premise reduction
`maximalLeviSupercuspidalUnitarizableConstituent_of_geometricLemma` uses, besides published
theorems, the length-two statement (VI.5.4), Casselman's criterion (VII.1.2) and Jacquet's
admissibility theorem (VI.2.2). This module discharges every input that the Library proves and
traces the three others to their published reductions. Only two open statements remain:

* `JointSpecialCompactBasisExistenceStatement` (Renard V.5.1–V.5.2), and
* condition (KF) of VI.3.4, `RationalNormKernelFixedLevelFinitenessStatement`, at the induced
  carrier universe `max u v`.

Only the sufficiency half of Casselman's criterion is used.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- Renard VII.1.3, unitarizable-constituent step, with the sufficiency half of Casselman's
criterion (VII.1.2) in place of the full criterion: the positive-exponent constituent, Casselman
sufficiency, Jacquet's admissibility theorem (VI.2.2) and ambient unimodularity give an
irreducible unitarizable subrepresentation or quotient. -/
theorem maximalLeviSupercuspidalUnitarizableConstituent_of_positiveConstituent_sufficiency
    (hPos : MaximalLeviSupercuspidalPositiveConstituentStatement.{u, v})
    (hSuff : ArbitraryParabolicCasselmanSufficiencyStatement.{u, max u v})
    (hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, max u v}) :
    MaximalLeviSupercuspidalUnitarizableConstituentStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul hnp hmax
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  intro ρ hρ hcusp hρc hred hπc
  obtain ⟨W, hW, hpos, hmap⟩ :=
    hPos k G hG P M U p l r hp hl hr hmul hnp hmax ρ hρ hcusp hρc hred hπc
  have hWc : Nonempty (UnitaryCentralCharacter W.representation) := by
    obtain ⟨c⟩ := hπc
    rcases hmap with ⟨f, hf⟩ | ⟨f, hf⟩
    · exact ⟨unitaryCentralCharacterOfInjective c f hf⟩
    · exact ⟨unitaryCentralCharacterOfSurjective c f hf⟩
  have hWadm : W.IsAdmissible := hAdm k G hG W hW
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  refine ⟨W, hW, ⟨rationalSquareIntegrableUnimodularForm G hG
    (RationalPointFamily.rationalReductiveUnimodularity k G hG standardCocharacter)
    W hW ?_⟩, hmap⟩
  intro _ _ haar _
  exact hSuff k G hG haar W hWadm hWc hpos

/-- The represented maximal-Levi length-two statement (Renard VI.5.4, (VII.1.3.2)) from the
joint special-compact basis statement and condition (KF) at the induced carrier universe. -/
theorem maximalLeviSupercuspidalLengthTwo_of_jointBasis_fixedLevel
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u})
    (hKF : CuspidalSupport.RationalNormKernelFixedLevelFinitenessStatement.{u, max u v}) :
    MaximalLeviSupercuspidalInductionLengthTwoStatement.{u, v} :=
  maximalLeviSupercuspidalLengthTwo_of_lengthBound
    (maximalLeviSupercuspidalLengthBound_of_cuspidalSplitting
      (representedCuspidalRemainderSplitting_of_fixedLevelFiniteness hKF parabolicDynamic
        smoothMaximalSplitTorusConjugacy standardCocharacter relativeRootSystem hJoint))

/-- The two-premise reduction of the unitarizable-constituent step of Renard VII.1.3: the joint
special-compact basis statement and condition (KF) of VI.3.4 at the induced carrier universe
imply `MaximalLeviSupercuspidalUnitarizableConstituentStatement`. -/
def MaximalLeviSupercuspidalUnitarizableConstituentLeafReductionStatement : Prop :=
  BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u} →
    CuspidalSupport.RationalNormKernelFixedLevelFinitenessStatement.{u, max u v} →
      MaximalLeviSupercuspidalUnitarizableConstituentStatement.{u, v}

/-- **Renard VII.1.3, unitarizable-constituent step, from two open inputs.** Every other input of
the published nine-premise reduction is a published theorem or is derived here from these two. -/
theorem maximalLeviSupercuspidalUnitarizableConstituent_of_jointBasis_fixedLevel :
    MaximalLeviSupercuspidalUnitarizableConstituentLeafReductionStatement.{u, v} := by
  intro hJoint hKF
  exact maximalLeviSupercuspidalUnitarizableConstituent_of_positiveConstituent_sufficiency
    (maximalLeviSupercuspidalPositiveConstituent_of_levi
      (maximalLeviSupercuspidalExponentTransfer_of_geometricLemma representedGeometricLemma
        maximalLeviContainment)
      (maximalLeviSupercuspidalLeviPositiveConstituent_of_geometricLemma representedGeometricLemma
        (maximalLeviSupercuspidalLengthTwo_of_jointBasis_fixedLevel hJoint hKF)
        maximalLeviConeComplement parabolicSelfNormalizer centerSplitComponentCompactness))
    (arbitraryParabolicCasselmanSufficiency_of_jointSpecialCompactBasis hJoint)
    (rationalPointsIrreducibleAdmissible_of_jacquetCartanDatum
      (rationalPointsJacquetCartanDatum_of hJoint standardCocharacter standardParabolicOrder))

end Langlands.Aubert.General.RepresentedParabolic
