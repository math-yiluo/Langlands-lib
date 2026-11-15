import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.SolvableRadicalQuotient

/-! # Semisimplicity through the solvable radical: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Semisimplicity through the solvable radical** (Milne, *Algebraic Groups* (2017),
6.44 and Proposition 19.10). Let `G` be a smooth connected affine group scheme over a
field `k`, and `k̄` the algebraic closure of `k`.

1. `G` is semisimple (the Library's `IsSemisimple`: connected reductive with finite
   scheme-theoretic centre) if and only if every smooth connected solvable normal closed
   subgroup of `G_{k̄}` is trivial. This is Milne's definition 6.44 of semisimplicity.
2. If `G` is connected reductive, then `G` is semisimple if and only if every smooth
   connected solvable normal closed subgroup of `G` over `k` itself is trivial:
   Proposition 19.10, (b) if and only if (c). -/
def SemisimpleRadicalCharacterizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      (IsSemisimple G ↔
        HasTrivialSolvableRadical ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)) ∧
      (IsConnectedReductive G → (IsSemisimple G ↔ HasTrivialSolvableRadical G))

end Langlands.GroupScheme
