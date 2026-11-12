import Langlands.GroupScheme.PseudoParabolicQuotientRationalLiftingProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusDescentReduction
import Langlands.GroupScheme.Rational.SolvableMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.NoProperPseudoParabolicSolvableEnvelopeProof
import Langlands.GroupScheme.PseudoParabolicStructureProof
import Langlands.GroupScheme.SplitTorusIntoPseudoParabolicReduction
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.PseudoParabolicQuotientPseudoCompleteAssembly
import Langlands.GroupScheme.SplitSolvableFixedPointProof
import Langlands.GroupScheme.PseudoParabolicRationalLiftingAssembly
import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalExistenceProof
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.GroupScheme.PseudoParabolicSplitRadicalProductProof
import Langlands.GroupScheme.PseudoParabolicSplitRadicalQuotientProof
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeRationalDensityProof
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeNormalityReduction
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Rational.RationalMaximalTorusDensityProof

/-! # Borel–Tits conjugacy of maximal split tori in smooth connected affine groups

The published reductions are instantiated with published proofs. Over infinite
fields, normality of the torus envelope comes from its compatibility with the
algebraic closure, so the open all-field normality statement is not used.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SmoothMaximalSplitTorusConjugacyProof

variable {k : Type u} [Field k]

/-- Over an infinite field, the fixed closed torus envelope of a smooth connected
affine group is normal on every test. -/
theorem torusGeneratedEnvelope_isNormal_of_infinite [Infinite k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (D : TorusGeneratedEnvelope G) : (SubgroupFunctor.range D.inclusion).IsNormal :=
  D.isNormal_of_algebraicClosure_envelope_eq
    (torusGeneratedEnvelopeAlgebraicClosureInfinite_of maximalTorusBaseChange
      maximalTorusConjugacy rationalMaximalTorusConjugateDensity k G)

/-- Over an infinite field, a smooth connected affine group whose split
unipotent radical has trivial image has the full rational-lifting property. -/
theorem rationalLiftingProperty_of_infinite_of_trivial_splitRadical [Infinite k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {N : GroupScheme (Spec (CommRingCat.of k))} (n : N ⟶ G)
    (hn : IsSplitUnipotentRadical n) (hzero : SubgroupFunctor.range n = ⊥) :
    PseudoParabolicRationalLiftingProperty G := by
  obtain ⟨D, hsmD, -, -⟩ := exists_pointed_torusDominated_envelope G
  let : Smooth D.group.X.hom := hsmD
  intro P i hi Q q hsep hlft hqc hsmq hsurjq hqcq hfib x
  let : IsSeparated Q.hom := hsep
  let : LocallyOfFiniteType Q.hom := hlft
  let : QuasiCompact Q.hom := hqc
  let : Smooth q.left := hsmq
  let : Surjective q.left := hsurjq
  let : QuasiCompact q.left := hqcq
  let E := DynamicParabolicPresentation.ofSplitProduct hi n hzero
    (fun U j hj χ T a => pseudoParabolicSplitRadicalProduct k G U N j n hj hn χ T a)
  exact D.rational_lifts_dynamic (torusGeneratedEnvelope_isNormal_of_infinite G D)
    (torusGeneratedEnvelopeRationalDensity k G D)
    i hi.isClosedSubgroup E.cocharacter E.range_eq q hfib x

end SmoothMaximalSplitTorusConjugacyProof

open SmoothMaximalSplitTorusConjugacyProof

/-- Every split subtorus can be conjugated by a rational point into any
pseudo-parabolic subgroup. -/
theorem splitTorusIntoPseudoParabolic : SplitTorusIntoPseudoParabolicStatement.{u} :=
  splitTorusIntoPseudoParabolic_of_components smoothSubgroupQuotientExistence
    pseudoParabolicSubgroupStructure pseudoParabolicQuotientPseudoComplete
    splitSolvablePseudoCompleteFixedPoint pseudoParabolicQuotientRationalLifting

/-- Borel–Tits (CGP Theorem C.2.3): over every field, any two maximal split tori
of a smooth connected affine group are conjugate by a rational point. -/
theorem smoothMaximalSplitTorusConjugacy : SmoothMaximalSplitTorusConjugacyStatement.{u} :=
  smoothMaximalSplitTorusConjugacy_of_solvable_of_envelope_of_structure_of_containment
    solvableMaximalSplitTorusConjugacy noProperPseudoParabolicSolvableEnvelope
    pseudoParabolicSubgroupStructure splitTorusIntoPseudoParabolic

end Langlands.GroupScheme
