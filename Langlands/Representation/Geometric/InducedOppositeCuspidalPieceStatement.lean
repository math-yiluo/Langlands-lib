import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Geometric.RefinementFunctors

/-!
# Cuspidal geometric pieces of opposite Jacquet modules of induction

A derived consequence of BZ77 2.12 and 2.4(d) for actual GL block Levis.
This file states it; it contains no proof.
-/

namespace Langlands

open GeneralLinear Geometric

universe uF uV uW

/-- An irreducible cuspidal representation occurring as an actual subquotient
of the opposite Jacquet module of an arbitrary smooth normalized induction is
an actual quotient of the permutation transport of a subrepresentation of one
upper refined Jacquet module of the inducing representation. -/
def GLInducedOppositeJacquetCuspidalPieceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B C : BlockShape n)
      (π : Rep.{uW} ℂ (B.Levi F.Carrier)), IsSmooth π.ρ →
      ∀ ρ : Rep.{uV} ℂ (C.Levi F.Carrier),
        Representation.IsIrreducible ρ.ρ →
        CuspidalSupport.IsLeviCuspidal C ρ.ρ →
        (∃ U : Subrepresentation (CuspidalJacquetMultiplicity.oppositeJacquet T C
            (CuspidalJacquetMultiplicity.induced T B π)).ρ,
          ∃ q : U.toRepresentation.IntertwiningMap ρ.ρ, Function.Surjective q) →
        ∃ (S : BlockRefinement B) (w : Equiv.Perm (Fin n))
          (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) (B.flatten S) C w)
          (U : Subrepresentation ((T.normalizedRefinedJacquet B S π.ρ).comp
            (flattenedLeviEquiv F.Carrier B S).toMonoidHom)),
          ∃ q : (CuspidalSupport.transport (B.flatten S) C w hw
              U.toRepresentation).IntertwiningMap ρ.ρ,
            Function.Surjective q

end Langlands
