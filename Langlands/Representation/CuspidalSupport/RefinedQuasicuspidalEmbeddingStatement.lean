import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Geometric.RefinementFunctors

/-! Normalized quasicuspidal embedding of irreducible representations of an
actual standard product Levi, from BZ76 Proposition 3.19. -/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

/-- Every irreducible smooth complex representation `ω` of an actual standard
product Levi `B.Levi F` has an injective intertwining map into the actual
normalized refined induction of an irreducible smooth quasicuspidal
representation `σ` of the Levi of the flattened shape `B.flatten S`, for some
block refinement `S`. The induced representation is formed from `σ` pulled
back along the inverse of the actual coordinate equivalence
`flattenedLeviEquiv`. All ranks and block shapes are included, the empty shape
at rank zero among them. The carrier universe `uV` of `ω` and `σ` is
independent of `uF`. -/
def NormalizedRefinedQuasicuspidalEmbeddingTheorem {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n) (ω : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    ω.IsIrreducible →
      ∃ (S : BlockRefinement B)
        (σ : SmoothRep.{0, uF, uV} ℂ ((B.flatten S).Levi F.Carrier)),
        σ.IsIrreducible ∧ IsLeviQuasicuspidal (B.flatten S) σ.representation ∧
          letI := T.leviTopologicalGroup B
          ∃ j : ω.representation.IntertwiningMap
              (T.normalizedRefinedInduced B S
                (σ.representation.comp
                  (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom)),
            Function.Injective j

end Langlands.CuspidalSupport
