import Langlands.ClassFieldTheory.Local.ClassFormationAbsoluteCorestrictionStatement
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyContinuousProof
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyRelativeImagesProof
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyInflationProof
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyRestrictionProof
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyArithmeticProof
import Langlands.ClassFieldTheory.Local.RelativeH1Proof
import Langlands.ClassFieldTheory.Local.InvariantRelativeConjugacyProof
import Langlands.ClassFieldTheory.Local.InvariantRelativeCorestrictionProof
import Langlands.ClassFieldTheory.Local.InvariantAbsoluteCorestrictionProof
import Langlands.ClassFieldTheory.Local.FundamentalConsequencesProof
import Langlands.ClassFieldTheory.Local.ClassFormationTateIsomorphismsProof
import Langlands.ClassFieldTheory.Local.ClassFormationInflationLawsProof
import Langlands.ClassFieldTheory.Local.ClassFormationTransferLawsProof
import Langlands.Cohomology.Tate.TateTheoremProof
import Langlands.ClassFieldTheory.Local.UnramifiedH2Proof

/-! # Simultaneous local class formation

The witness is the local invariant family built from the proved unramified
`H²` exhaustion. Its five family laws are proved directly; every other clause is a
generic consequence of the finite class-formation axioms, invariant conjugacy,
or the continuous invariant properties.
-/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Tate's cup-product theorem and unramified `H²` exhaustion give all fifteen
conclusions for the local invariant family. -/
theorem localAbsoluteCorestrictionCompatibleClassFormation_of
    (hTate : Langlands.Tate.TateCupIsomorphism.{u})
    (hEx : UnramifiedH2Exhaustion.{u}) :
    LocalAbsoluteCorestrictionCompatibleClassFormationStatement.{u} := by
  intro p _
  let I := localInvariantFamily hEx p
  have hCont : I.ContinuousInvariantProperties := localInvariantFamilyContinuous hEx p
  have hRCF : I.RelativeClassFormation :=
    ⟨fun F L _ _ _ _ => finiteRelativeH1Vanishing F.Carrier L,
      localInvariantFamilyRelativeImages hEx p, localInvariantFamilyInflation hEx p,
      localInvariantFamilyRestriction hEx p⟩
  have hConj : I.RelativeConjugacy :=
    invariantRelativeConjugacy p I hRCF.2.2.1 hRCF.2.2.2
  obtain ⟨hFund, hFInf, hFRes, hFCor, hFConj⟩ :=
    relativeFundamentalClassConsequences p I hRCF hConj
  obtain ⟨hPosInf, hOrdInf⟩ := classFormationInflationLaws p I hRCF
  exact ⟨I, localInvariantFamilyArithmetic hEx p, hCont, hRCF, hConj,
    invariantRelativeCorestriction p I hRCF.2.1 hRCF.2.2.2,
    hFund, hFInf, hFRes, hFCor, hFConj,
    classFormationTateIsomorphisms hTate p I hRCF, hPosInf,
    classFormationTransferLaws p I hRCF, hOrdInf,
    invariantAbsoluteCorestriction p I hCont.2.1 hCont.2.2.1⟩

/-- With Tate's theorem proved, unramified `H²` exhaustion alone gives all
fifteen conclusions. -/
theorem localAbsoluteCorestrictionCompatibleClassFormation_of_exhaustion
    (hEx : UnramifiedH2Exhaustion.{u}) :
    LocalAbsoluteCorestrictionCompatibleClassFormationStatement.{u} :=
  localAbsoluteCorestrictionCompatibleClassFormation_of Langlands.Tate.tateCupIsomorphism hEx

/-- Simultaneous local class formation with invariant corestriction and Tate
reciprocity, unconditionally. -/
theorem localAbsoluteCorestrictionCompatibleClassFormation :
    LocalAbsoluteCorestrictionCompatibleClassFormationStatement.{u} :=
  localAbsoluteCorestrictionCompatibleClassFormation_of_exhaustion unramifiedH2Exhaustion

end Langlands.ClassFieldTheory.Local
