import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof
import Langlands.Representation.Filtration.ObjectTransport
import Langlands.Representation.Parabolic.OppositeJacquetFiltration
import Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof

/-! Transport a supplied upper Jacquet filtration to the actual composed
opposite Jacquet quotient, without changing its indices. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear
open OppositeCuspidalJacquetFiltration

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
  (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))

/-- Pull back a filtration of the upper Jacquet module for the reversed
shape, then transport it through the actual normalized reversal equivalence. -/
def oppositeFiltrationOfReverse {l : ℕ}
    (s : ObjectRepFiltration (Rep.of (T.normalizedJacquet B.reverse A.ρ)) l) :
    ObjectRepFiltration (CuspidalJacquetMultiplicity.oppositeJacquet T B A) l :=
  LengthTwo.transport (oppositeJacquetReverseEquiv T B A)
    (s.comp (leviReverseEquiv B).toMonoidHom)

/-- Membership retains the original step and uses the inverse of the
constructed normalized reversal map. -/
@[simp]
theorem mem_oppositeFiltrationOfReverse {l : ℕ}
    (s : ObjectRepFiltration (Rep.of (T.normalizedJacquet B.reverse A.ρ)) l)
    (k : Fin (l + 1)) (v : CuspidalJacquetMultiplicity.oppositeJacquet T B A) :
    v ∈ (oppositeFiltrationOfReverse T B A s).subrepresentation k ↔
      (oppositeJacquetReverseEquiv T B A).symm v ∈ s.subrepresentation k :=
  Iff.rfl

/-- Each reversed upper grade, pulled back along block relabelling, is
equivalent to the grade at the same index in the opposite filtration. -/
def oppositeFiltrationOfReverseGradedEquiv {l : ℕ}
    (s : ObjectRepFiltration (Rep.of (T.normalizedJacquet B.reverse A.ρ)) l)
    (i : Fin l) :
    Representation.Equiv
      ((s.gradedRepresentation i).ρ.comp (leviReverseEquiv B).toMonoidHom)
      ((oppositeFiltrationOfReverse T B A s).gradedRepresentation i).ρ :=
  (s.compGradedEquiv (leviReverseEquiv B).toMonoidHom i).symm.trans
    ((s.comp (leviReverseEquiv B).toMonoidHom).equivTransportGradedEquiv
      (oppositeJacquetReverseEquiv T B A) i)

variable (S : BlockRefinement B)

/-- Choose the already proved actual opposite transitivity equivalence.
Its representative formula is retained below. -/
def oppositeRefinementFiltrationEquiv :
    (T.normalizedRefinedOppositeJacquet B S
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ).Equiv
        (T.normalizedComposedOppositeJacquet B S A.ρ) :=
  Classical.choose
    (Parabolic.normalizedOppositeRefinementTransitivity p F T n B S A)

@[simp]
theorem oppositeRefinementFiltrationEquiv_mk (v : A) :
    oppositeRefinementFiltrationEquiv T B A S
      (refinedOppositeJacquetMk B S
        (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
        (Jacquet.mk A.ρ (B.oppositeUnipotentSubgroup F.Carrier) v)) =
      Parabolic.composedOppositeJacquetMk B S A.ρ v :=
  Classical.choose_spec
    (Parabolic.normalizedOppositeRefinementTransitivity p F T n B S A) v

/-- Take the actual refined opposite Jacquet images of the reversed
filtration and identify the iterated quotient with the composed quotient. -/
def composedOppositeFiltrationOfReverse {l : ℕ}
    (s : ObjectRepFiltration (Rep.of (T.normalizedJacquet B.reverse A.ρ)) l) :
    ObjectRepFiltration (Rep.of (T.normalizedComposedOppositeJacquet B S A.ρ)) l :=
  LengthTwo.transport (oppositeRefinementFiltrationEquiv T B A S)
    (T.normalizedRefinedOppositeJacquetFiltration B S
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
      (oppositeFiltrationOfReverse T B A s))

/-- A direct composed-quotient class is in a step exactly when its inverse
transitivity class has a representative in the corresponding opposite step. -/
theorem mem_composedOppositeFiltrationOfReverse {l : ℕ}
    (s : ObjectRepFiltration (Rep.of (T.normalizedJacquet B.reverse A.ρ)) l)
    (k : Fin (l + 1))
    (q : Parabolic.ComposedOppositeJacquetModule B S A.ρ) :
    q ∈ (composedOppositeFiltrationOfReverse T B A S s).subrepresentation k ↔
      ∃ v : CuspidalJacquetMultiplicity.oppositeJacquet T B A,
        v ∈ (oppositeFiltrationOfReverse T B A s).subrepresentation k ∧
        refinedOppositeJacquetMk B S
          (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ v =
            (oppositeRefinementFiltrationEquiv T B A S).symm q :=
  Iff.rfl

set_option maxHeartbeats 800000 in
/-- The direct composed filtration and the intermediate image filtration
have equivalent actual grades at exactly the same indices. -/
def composedOppositeFiltrationOfReverseGradedEquiv {l : ℕ}
    (s : ObjectRepFiltration (Rep.of (T.normalizedJacquet B.reverse A.ρ)) l)
    (i : Fin l) :
    ((T.normalizedRefinedOppositeJacquetFiltration B S
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
      (oppositeFiltrationOfReverse T B A s)).gradedRepresentation i).ρ.Equiv
        ((composedOppositeFiltrationOfReverse T B A S s).gradedRepresentation i).ρ :=
  ObjectRepFiltration.equivTransportGradedEquiv
    (A := Rep.of (T.normalizedRefinedOppositeJacquet B S
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ))
    (B := Rep.of (T.normalizedComposedOppositeJacquet B S A.ρ))
    (T.normalizedRefinedOppositeJacquetFiltration B S
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
      (oppositeFiltrationOfReverse T B A s))
    (oppositeRefinementFiltrationEquiv T B A S) i

end Langlands.Geometric
