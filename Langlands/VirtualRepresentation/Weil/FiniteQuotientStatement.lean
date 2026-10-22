import Langlands.VirtualRepresentation.Weil.Realization
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Finite-quotient realization of the actual irreducible lattice

The lattice, representation classes, induction and trace maps are genuine
constructions. The assertions identifying their images and pairings are
separate proposition definitions, not fields of those constructions.
-/

noncomputable section

namespace Langlands.VirtualRepresentation.Weil

universe uG uV uH

variable (G : Type uG) [Group G] [TopologicalSpace G]
variable (H : Type uH) [Group H]

/-- Classes factoring through a finite quotient have finite image and are
unitarizable. The two conditions remain distinct predicates. -/
def FiniteQuotientUnitaryStatement [Fintype H] : Prop :=
  ∀ [IsTopologicalGroup G] (f : G →* H),
    Function.Surjective f → IsOpen (f.ker : Set G) →
      factoringSupported.{uG, uV, uH} G f ≤ finiteImageSupported G ∧
      factoringSupported.{uG, uV, uH} G f ≤ unitarySupported G

/-- Trace realization is injective on the actual finite-quotient supported
irreducible lattice; no faithfulness on arbitrary split representations is assumed. -/
def FiniteQuotientTraceFaithfulnessStatement [Fintype H] : Prop :=
  ∀ [IsTopologicalGroup G] (f : G →* H),
    Function.Surjective f → IsOpen (f.ker : Set G) →
      Set.InjOn (traceCharacter.{uG, uV} G) (factoringSupported G f)

/-- Integral rank degree agrees with the trace at the identity. -/
def FiniteQuotientDegreeStatement [Fintype H] : Prop :=
  ∀ [IsTopologicalGroup G] (f : G →* H),
    Function.Surjective f → IsOpen (f.ker : Set G) →
      ∀ x : IrreducibleLattice.{uG, uV} G,
        x ∈ factoringSupported G f →
          (degree G x : ℂ) = traceCharacter G x 1

/-- The integral coefficient pairing becomes the normalized finite-character
inner product on the quotient. Conjugation is on the second character. -/
def FiniteQuotientPairingStatement [Fintype H] : Prop :=
  ∀ [IsTopologicalGroup G] (f : G →* H),
    Function.Surjective f → IsOpen (f.ker : Set G) →
      ∀ x y : IrreducibleLattice.{uG, uV} G,
        x ∈ factoringSupported G f → y ∈ factoringSupported G f →
          ∀ a b : H → ℂ,
            (∀ g : G, traceCharacter G x g = a (f g)) →
            (∀ g : G, traceCharacter G y g = b (f g)) →
              (multiplicityPairing G x y : ℂ) =
                (Fintype.card H : ℂ)⁻¹ * ∑ h : H, a h * star (b h)

/-- Actual rank-one subgroup induction, inflated along an open finite quotient,
has an effective irreducible decomposition of degree equal to the subgroup index.
This positivity assertion precedes the signed Brauer spanning assertion. -/
def FiniteQuotientPositiveInductionStatement [Fintype H] : Prop :=
  ∀ [IsTopologicalGroup G] (f : G →* H),
    Function.Surjective f → IsOpen (f.ker : Set G) →
      ∀ d : FiniteRep.MonomialDatum ℂ H,
        ∃ x : IrreducibleLattice.{uG, uV} G,
          x ∈ factoringSupported G f ∧ x ∈ effective ∧
          realizeVirtual G x = inflatedMonomial G f d ∧
          degree G x = (d.1.index : ℤ)

/-- Integral Brauer spanning sends the factoring support into both actual
preimages. This does not assert a converse for arbitrary representations of G. -/
def FiniteQuotientBrauerSpanningStatement [Fintype H] : Prop :=
  ∀ [IsTopologicalGroup G] (f : G →* H),
    Function.Surjective f → IsOpen (f.ker : Set G) →
      factoringSupported.{uG, uV, uH} G f ≤ inducedVirtualPreimage G f ∧
      factoringSupported.{uG, uV, uH} G f ≤ inducedTracePreimage G f

/-- Realization restricts to a bijection from the factoring-supported
irreducible lattice onto the actual inflated monomial span. -/
def FiniteQuotientSpanBijectionStatement [Fintype H] : Prop :=
  ∀ [IsTopologicalGroup G] (f : G →* H),
    Function.Surjective f → IsOpen (f.ker : Set G) →
      Set.BijOn (realizeVirtual.{uG, uV} G)
        (factoringSupported G f) (inflatedMonomialSpan G f)

/-- Finite-quotient representation prerequisites on actual classes and lattices.
This does not construct a local Weil quotient or an automorphic image. -/
def FiniteQuotientRealizationStatement [Fintype H] : Prop :=
  FiniteQuotientUnitaryStatement.{uG, uV, uH} G H ∧
  FiniteQuotientTraceFaithfulnessStatement.{uG, uV, uH} G H ∧
  FiniteQuotientDegreeStatement.{uG, uV, uH} G H ∧
  FiniteQuotientPairingStatement.{uG, uV, uH} G H ∧
  FiniteQuotientPositiveInductionStatement.{uG, uV, uH} G H ∧
  FiniteQuotientBrauerSpanningStatement.{uG, uV, uH} G H ∧
  FiniteQuotientSpanBijectionStatement.{uG, uV, uH} G H

end Langlands.VirtualRepresentation.Weil
