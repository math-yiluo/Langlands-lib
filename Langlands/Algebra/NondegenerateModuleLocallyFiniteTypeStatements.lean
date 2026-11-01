import Langlands.Algebra.NondegenerateModuleAbelianProof
import Langlands.CategoryTheory.Renard.LocallyFiniteType

/-!
# Renard I.6: local finite type of actual nondegenerate modules

The source calls this condition AB6 and distinguishes it from Grothendieck's
AB6. The explicit finite-subset family has the original carrier's size.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NondegenerateModuleLocallyFiniteTypeStatements

open CategoryTheory

universe uA uM

/-- An increasing family indexed by finite subsets of the original carrier
covers each object by actual finite-type subobjects, containing those subsets. -/
def DirectedFiniteTypeCoverStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
    ∀ M : NondegenerateModuleCat.{uA, uM} A,
      ∃ F : Finset M.obj → Subobject M,
        Monotone F ∧
          (∀ S, Langlands.Renard.IsFiniteTypeObject (F S : NondegenerateModuleCat A)) ∧
          (∀ S (m : M.obj), m ∈ S →
            ∃ x : (F S : NondegenerateModuleCat A).obj,
              (F S).arrow.hom.toAddMonoidHom x = m) ∧
          IsLUB (Set.range F) (⊤ : Subobject M)

/-- Every actual nondegenerate object is a sum of its finite-type subobjects:
Renard's source AB6, with the named abelian structure. -/
def SourceAB6Statement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
    Langlands.Renard.SourceAB6 (NondegenerateModuleCat.{uA, uM} A)

/-- The explicit increasing finite-type cover and the canonical source AB6 law. -/
def LocallyFiniteTypeAssertions : Prop :=
  DirectedFiniteTypeCoverStatement.{uA, uM} ∧ SourceAB6Statement.{uA, uM}

example : Prop := DirectedFiniteTypeCoverStatement.{uA, uM}
example : Prop := SourceAB6Statement.{uA, uM}
example : Prop := LocallyFiniteTypeAssertions.{uA, uM}
example : Prop := LocallyFiniteTypeAssertions.{0, 1}
example : Prop := LocallyFiniteTypeAssertions.{1, 0}

/-- The category condition is the canonical finite-type-subobject least upper bound. -/
example : SourceAB6Statement.{uA, uM} ↔
    (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
      letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
      ∀ M : NondegenerateModuleCat.{uA, uM} A,
        IsLUB {P : Subobject M |
          Langlands.Renard.IsFiniteTypeObject (P : NondegenerateModuleCat A)}
          (⊤ : Subobject M)) := Iff.rfl

end Langlands.Algebra.NondegenerateModuleLocallyFiniteTypeStatements
