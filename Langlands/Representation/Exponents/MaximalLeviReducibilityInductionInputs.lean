import Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.ParabolicPresentationUnitarity
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityStatement
import Langlands.GroupScheme.Rational.ParabolicRootPresentationStatement
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero

/-! # The induction inputs of the unitary case of Renard VII.1.3

Three of the input statements of `MaximalLeviReducibilityUnitaryInputs` concern normalized
induction from an actual rational parabolic alone. This module proves them:

* `LeviInductionNontrivialStatement` outright, since the Levi projection of a represented
  parabolic is continuous;
* `LeviInductionAdmissibleStatement` from the published compactness statement
  `ArbitraryParabolicQuotientCompactStatement` (Renard III.2.3);
* `LeviInductionUnitarizableStatement` from compactness, the published unimodularity
  statement `RationalReductiveUnimodularityStatement` (with its standard-cocharacter
  premise) and the published existence statement for root presentations
  `ParabolicRootPresentationExistenceStatement`, which together give the modular
  character of the parabolic (Renard IV.2.3, V.5.4).
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- Normalized induction from an actual rational parabolic is nonzero on nonzero
representations: the Levi projection of the represented parabolic is continuous. -/
theorem leviInductionNontrivial : LeviInductionNontrivialStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  let := leviPointTopology l hl
  intro σ _
  have : Nontrivial (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ) :=
    inferInstanceAs (Nontrivial σ)
  exact nontrivial_normalizedInduction
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (continuous_projection_pointImage p l r hp hl hr hmul)
    (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)

/-- Renard III.2.3: normalized induction from an actual rational parabolic preserves
admissibility, given compactness of the parabolic quotient. -/
theorem leviInductionAdmissible_of_quotientCompact
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u}) :
    LeviInductionAdmissibleStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul σ hσ
  exact leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement hCompact hG
    p l r hp hl hr hmul σ hσ

/-- Renard IV.2.3: normalized induction from an actual rational parabolic preserves
unitarizability, given compactness of the parabolic quotient, unimodularity of reductive
groups and existence of root presentations of parabolics (which give the modular
character of the parabolic, Renard V.5.4). -/
theorem leviInductionUnitarizable_of_inputs
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u})
    (hPres : ParabolicRootPresentationExistenceStatement.{u}) :
    LeviInductionUnitarizableStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  intro σ ⟨b⟩
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : T2Space (rationalPoints M) := rationalPoint_t2Space k M
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) := hCompact k G hG P p hp
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hl.isConnectedReductive).1
  obtain ⟨pres⟩ := hPres k G hG P M A p l a hp hl ha
  exact ⟨leviInductionUnimodularForm p l r hp hr hl hmul (hUnimod k G hG hStandard)
    (modularCharacter_of_presentation hG p l r hp hl hr hmul pres
      (hUnimod k M hl.isConnectedReductive hStandard)) σ b⟩

end Langlands.Aubert.General.RepresentedParabolic
