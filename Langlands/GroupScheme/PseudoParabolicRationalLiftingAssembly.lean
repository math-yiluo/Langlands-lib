import Langlands.GroupScheme.PseudoParabolicSplitRadicalInduction
import Langlands.GroupScheme.PseudoParabolicDynamicPresentation
import Langlands.GroupScheme.PseudoParabolicFiniteFieldLifting
import Langlands.GroupScheme.PseudoParabolicSplitRadicalProductStatement
import Langlands.GroupScheme.PseudoParabolicSplitRadicalQuotientStatement
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeDomination
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeLifting
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeNormalityStatement
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeRationalDensityStatement

/-! # Assembly of rational lifting from structural inputs

The finite-field branch is unconditional. Over infinite fields the trivial
split-radical case follows from the exact product theorem and normality and
density of the fixed torus envelope. The published dimension induction then
gives the exact all-field target, conditional on the named structural inputs.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.PseudoParabolicRationalLiftingAssembly

variable {k : Type u} [Field k]

/-- The entire fixed-group rational-lifting property holds over a finite field
for an affine ambient group, using the original supplied quotient maps. -/
theorem property_of_finite [Finite k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    PseudoParabolicRationalLiftingProperty G := by
  intro P i hi Q q _ _ _ hsmq hsurjq hqcq hfib x
  let : Smooth q.left := hsmq
  let : Surjective q.left := hsurjq
  let : QuasiCompact q.left := hqcq
  exact HomogeneousQuotient.rational_lifts_pseudo_finiteField k G P i q hi hfib x

/-- In the infinite-field trivial split-radical case, exact product replacement
and the normality and density statements supply the full fixed-group property.
All three structural propositions remain explicit inputs. -/
theorem property_of_trivial_split_radical [Infinite k]
    (hproduct : PseudoParabolicSplitRadicalProductStatement.{u})
    (hnormal : TorusGeneratedEnvelopeNormalityStatement.{u})
    (hdensity : TorusGeneratedEnvelopeRationalDensityStatement.{u})
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
    (fun U j hj χ T a => hproduct k G U N j n hj hn χ T a)
  exact D.rational_lifts_dynamic (hnormal k G D) (hdensity k G D)
    i hi.isClosedSubgroup E.cocharacter E.range_eq q hfib x

/-- The named structural propositions imply the exact published all-field
rational-lifting target. This conditional assembly does not prove its inputs. -/
theorem statement_of_structural_inputs
    (hrad : SplitUnipotentRadicalExistenceStatement.{u})
    (hquot : NormalSubgroupQuotientStatement.{u})
    (htor : SplitUnipotentAffineTorsorStatement.{u})
    (hproduct : PseudoParabolicSplitRadicalProductStatement.{u})
    (hdescent : PseudoParabolicSplitRadicalQuotientStatement.{u})
    (hnormal : TorusGeneratedEnvelopeNormalityStatement.{u})
    (hdensity : TorusGeneratedEnvelopeRationalDensityStatement.{u}) :
    PseudoParabolicQuotientRationalLiftingStatement.{u} := by
  apply PseudoParabolicSplitRadicalInduction.statement_of_trivial_split_radical
    hrad hquot htor hdescent
  intro k _ G _ _ _ N n hn hzero
  obtain hfinite | hinfinite := finite_or_infinite k
  · let : Finite k := hfinite
    exact property_of_finite G
  · let : Infinite k := hinfinite
    exact property_of_trivial_split_radical hproduct hnormal hdensity G n hn hzero

/-- Choose an actual lift, with its exact equation under the original supplied
projection, from the explicit structural propositions used in the assembly. -/
def liftOfStructuralInputs
    (hrad : SplitUnipotentRadicalExistenceStatement.{u})
    (hquot : NormalSubgroupQuotientStatement.{u})
    (htor : SplitUnipotentAffineTorsorStatement.{u})
    (hproduct : PseudoParabolicSplitRadicalProductStatement.{u})
    (hdescent : PseudoParabolicSplitRadicalQuotientStatement.{u})
    (hnormal : TorusGeneratedEnvelopeNormalityStatement.{u})
    (hdensity : TorusGeneratedEnvelopeRationalDensityStatement.{u})
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : P ⟶ G) (hi : IsPseudoParabolicSubgroup i)
    (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q)
    [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q) :
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X // g ≫ q = x} :=
  Classical.indefiniteDescription _ (statement_of_structural_inputs
    hrad hquot htor hproduct hdescent hnormal hdensity k G inferInstance P i hi
    Q q inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance hfib x)

end Langlands.GroupScheme.PseudoParabolicRationalLiftingAssembly
