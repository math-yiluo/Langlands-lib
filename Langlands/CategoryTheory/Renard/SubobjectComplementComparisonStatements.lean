import Langlands.CategoryTheory.RenardSemisimplicity
import Mathlib.Order.Disjoint

/-!
# Canonical subobject decompositions and lattice complements

Internal comparison statements motivated by Renard 2026 A.VI.2(9),
printed page 263 / PDF269, and A.VII(iii), printed page 265 / PDF271.
This module defines propositions only.
-/

universe u v

open CategoryTheory Limits

namespace Langlands.Renard

/-- The canonical binary-coproduct comparison for two actual subobjects is an
isomorphism exactly when their intersection is zero and their sum is the whole
object. The reverse implication is the existing Noether complement statement;
the full equivalence is an internal comparison target. -/
def CanonicalSubobjectComplementStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ (X : C) (P Q : Subobject X),
    IsIso (coprod.desc P.arrow Q.arrow) ↔
      P ⊓ Q = ⊥ ∧ P ⊔ Q = ⊤

/-- The published canonical-map complement condition agrees with the actual
bounded subobject lattice being complemented. `ComplementedLattice` is the
right-hand proposition, not an additional typeclass hypothesis. -/
def EverySubobjectComplementedLatticeStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ X : C,
    EverySubobjectHasComplement X ↔ ComplementedLattice (Subobject X)

/-- The closed internal comparison family for canonical subobject complements
in an arbitrary abelian category. -/
def SubobjectComplementComparisonStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  CanonicalSubobjectComplementStatement C ∧
    EverySubobjectComplementedLatticeStatement C

end Langlands.Renard
