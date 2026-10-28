import Langlands.CategoryTheory.RenardExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Sequence exactness, exact short complexes and homology

These proposition targets are derived interface comparisons with Mathlib.
Renard A.VIII.1 supplies the sequence definitions and forward finite
preservation assertions, rather than explicitly stating these equivalences.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace Langlands.Renard

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]

/-- Compare source sequence exactness with preservation of every middle-exact short complex. -/
def SequenceExactShortComplexStatement (F : C ⥤ D) [F.Additive] : Prop :=
  SequenceExact F ↔
    (∀ S : ShortComplex C, S.Exact → (S.map F).Exact)

/-- Compare source sequence exactness with preservation of short exact complexes. -/
def SequenceExactShortExactStatement (F : C ⥤ D) [F.Additive] : Prop :=
  SequenceExact F ↔
    (∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact)

/-- Compare source sequence exactness with Mathlib's actual homology-preservation class. -/
def SequenceExactHomologyStatement (F : C ⥤ D) [F.Additive] : Prop :=
  SequenceExact F ↔ F.PreservesHomology

/-- Aggregate proposition for the three derived exactness and homology comparisons. -/
def ExactnessHomologyComparisonStatement (F : C ⥤ D) [F.Additive] : Prop :=
  SequenceExactShortComplexStatement F ∧
    (SequenceExactShortExactStatement F ∧ SequenceExactHomologyStatement F)

end Langlands.Renard
