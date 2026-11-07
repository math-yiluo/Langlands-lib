import Langlands.Representation.Exponents.MaximalLeviSupercuspidalPositiveConstituentStatement
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalExponentTransferReduction
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalLeviPositiveConstituentReduction
import Langlands.Representation.Exponents.ArbitraryParabolicCasselmanStatement
import Langlands.Representation.Exponents.CasselmanSufficiencyAssembly
import Langlands.Representation.Exponents.ArbitraryParabolicUnitarity
import Langlands.Representation.Exponents.JacquetNontrivialityTransfer
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityStatement
import Langlands.Representation.Aubert.General.IrreducibleAdmissibleStatement
import Langlands.GroupScheme.Rational.CenterSplitComponentCompactnessProof

/-! # The unitarizable-constituent step of Renard VII.1.3 as a reduction

Renard 2026, VII.1.3 (PDF pp.230–232), obtains an irreducible unitarizable constituent of a
reducible `i_P^G ρ` by showing that one of its constituents satisfies the exponent condition of
Casselman's criterion (VII.1.2), so that it is square-integrable modulo the centre and hence
unitarizable (IV.3.2).

This module assembles that step from the published reductions of its two exponent parts:

* the constituent step (`maximalLeviSupercuspidalLeviPositiveConstituent_of_geometricLemma`):
  one of `π₁, π₂` has its exponents in the positive cones along the parabolics with Levi
  factor `M`;
* the transfer step (`maximalLeviSupercuspidalExponentTransfer_of_geometricLemma`): such a
  constituent has its exponents in the positive cones along every actual parabolic.

Casselman's criterion, Jacquet's admissibility theorem and the unimodularity of `G(F)` then
make that constituent unitarizable. The compactness of the centre modulo a split component
is supplied by the published `centerSplitComponentCompactness`; the remaining nine inputs are
premises of `MaximalLeviSupercuspidalUnitarizableConstituentReductionStatement`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- The constituent step and the transfer step give the positive-exponent constituent of a
reducible maximal-Levi supercuspidal induction. -/
theorem maximalLeviSupercuspidalPositiveConstituent_of_levi
    (hTransfer : MaximalLeviSupercuspidalExponentTransferStatement.{u, v})
    (hConstituent : MaximalLeviSupercuspidalLeviPositiveConstituentStatement.{u, v}) :
    MaximalLeviSupercuspidalPositiveConstituentStatement.{u, v} := by
  intro k _ _ _ _ _ G hG _ _ P M U p l r hp hl hr hmul hproper hmax ρ hρ hsc hρu hred hπu
  obtain ⟨W, hW, hpos, hmap⟩ :=
    hConstituent k G hG P M U p l r hp hl hr hmul hproper hmax ρ hρ hsc hρu hred hπu
  exact ⟨W, hW,
    hTransfer k G hG P M U p l r hp hl hr hmul hproper hmax ρ hρ hsc hπu W hmap hpos, hmap⟩

/-- Renard VII.1.3, unitarizable-constituent step: the positive-exponent constituent,
Casselman's criterion (VII.1.2), Jacquet's admissibility theorem (VI.2.2) and ambient
unimodularity give an irreducible unitarizable subrepresentation or quotient. -/
theorem maximalLeviSupercuspidalUnitarizableConstituent_of_positiveConstituent
    (hPos : MaximalLeviSupercuspidalPositiveConstituentStatement.{u, v})
    (hCass : ArbitraryParabolicCasselmanCriterionStatement.{u, max u v})
    (hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, max u v})
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u}) :
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
    (hUnimod k G hG hStandard) W hW ?_⟩, hmap⟩
  intro _ _ haar _
  exact (hCass k G hG haar W hWadm hWc).mpr hpos

/-- Renard VII.1.3, unitarizable-constituent step, as a conditional statement: the
represented geometric lemma, the containment of maximal Levi subgroups, the length-two
statement, the cone complement statement, the self-normalizing property of parabolics,
Casselman's criterion, Jacquet's admissibility theorem, the unimodularity of `G(F)` and the
standard-cocharacter statement give the unitarizable-constituent statement. -/
def MaximalLeviSupercuspidalUnitarizableConstituentReductionStatement : Prop :=
  RepresentedGeometricLemmaStatement.{u, v} →
    MaximalLeviContainmentStatement.{u} →
      MaximalLeviSupercuspidalInductionLengthTwoStatement.{u, v} →
        MaximalLeviConeComplementStatement.{u} →
          ParabolicSelfNormalizerStatement.{u} →
            ArbitraryParabolicCasselmanCriterionStatement.{u, max u v} →
              RationalPointsIrreducibleAdmissibleStatement.{u, max u v} →
                RationalPointFamily.RationalReductiveUnimodularityStatement.{u} →
                  StandardCocharacterStatement.{u} →
                    MaximalLeviSupercuspidalUnitarizableConstituentStatement.{u, v}

/-- **Renard VII.1.3, unitarizable-constituent step.** The nine premises of
`MaximalLeviSupercuspidalUnitarizableConstituentReductionStatement`, together with the
published compactness of the centre modulo a split component, give the
unitarizable-constituent statement. -/
theorem maximalLeviSupercuspidalUnitarizableConstituent_of_geometricLemma :
    MaximalLeviSupercuspidalUnitarizableConstituentReductionStatement.{u, v} := by
  intro hgeo hS2 hlen hcone hnorm hCass hAdm hUnimod hStandard
  exact maximalLeviSupercuspidalUnitarizableConstituent_of_positiveConstituent
    (maximalLeviSupercuspidalPositiveConstituent_of_levi
      (maximalLeviSupercuspidalExponentTransfer_of_geometricLemma hgeo hS2)
      (maximalLeviSupercuspidalLeviPositiveConstituent_of_geometricLemma hgeo hlen hcone hnorm
        centerSplitComponentCompactness))
    hCass hAdm hUnimod hStandard

end Langlands.Aubert.General.RepresentedParabolic
