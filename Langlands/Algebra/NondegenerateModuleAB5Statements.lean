import Langlands.Algebra.NondegenerateModuleAbelianProof
import Langlands.CategoryTheory.RenardGrothendieckAxioms

/-!
# Renard I.6: source AB5 for the actual nondegenerate module category

The directed subobject law is independent of the index size. The complete
source AB5 assertion bounds the index universe by the displayed carrier.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NondegenerateModuleAB5Statements

universe uA uI uM

/-- Intersection distributes over sums of arbitrary-size nonempty directed
families in the existing categorical subobject order. -/
def DirectedSubobjectDistributivity : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
    Langlands.Renard.DirectedSubobjectSumsDistribute.{uI}
      (NondegenerateModuleCat.{uA, uM} A)

/-- Source AB5: index-sized coproducts and directed subobject distributivity,
using the named actual abelian structure and a sufficiently large carrier. -/
def SourceAB5Statement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
    Langlands.Renard.SourceAB5.{uI}
      (NondegenerateModuleCat.{uA, max uI uM} A)

/-- The directed-sum law and the entire sized source AB5 assertion. -/
def AB5Assertions : Prop :=
  DirectedSubobjectDistributivity.{uA, uI, uM} ∧
    SourceAB5Statement.{uA, uI, uM}

/-! Complete closed interfaces retain all three independent universes. -/
example : Prop := DirectedSubobjectDistributivity.{uA, uI, uM}
example : Prop := SourceAB5Statement.{uA, uI, uM}
example : Prop := AB5Assertions.{uA, uI, uM}
example : Prop := AB5Assertions.{0, 1, 0}
example : Prop := AB5Assertions.{1, 0, 0}
example : Prop := AB5Assertions.{0, 0, 1}
example : Prop := AB5Assertions.{0, 1, 2}
example : Prop := AB5Assertions.{0, 2, 1}
example : Prop := AB5Assertions.{1, 0, 2}
example : Prop := AB5Assertions.{1, 2, 0}
example : Prop := AB5Assertions.{2, 0, 1}
example : Prop := AB5Assertions.{2, 1, 0}

/-- The first assertion uses the categorical intersection and its actual order,
and requires both least upper bounds to exist. -/
example : DirectedSubobjectDistributivity.{uA, uI, uM} ↔
    (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
      letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
      ∀ (M : NondegenerateModuleCat.{uA, uM} A) (I : Type uI), Nonempty I →
        ∀ F : I → CategoryTheory.Subobject M, Directed (· ≤ ·) F →
          ∀ N : CategoryTheory.Subobject M, ∃ U : CategoryTheory.Subobject M,
            IsLUB (Set.range F) U ∧
              IsLUB (Set.range fun i => N ⊓ F i) (N ⊓ U)) := Iff.rfl

/-- The second assertion includes actual coproduct existence. -/
example : SourceAB5Statement.{uA, uI, uM} ↔
    (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
      letI := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
      CategoryTheory.Limits.HasCoproducts.{uI}
          (NondegenerateModuleCat.{uA, max uI uM} A) ∧
        Langlands.Renard.DirectedSubobjectSumsDistribute.{uI}
          (NondegenerateModuleCat.{uA, max uI uM} A)) := Iff.rfl

end Langlands.Algebra.NondegenerateModuleAB5Statements
