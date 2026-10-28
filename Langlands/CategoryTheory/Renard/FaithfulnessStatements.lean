import Langlands.CategoryTheory.RenardExactFunctor

/-!
# Renard's criteria for faithful additive functors

Renard A.VIII.1 states the sufficient zero-morphism criterion and the
exact-plus-zero-object-reflection lemma. The necessary direction of the
first equivalence and the aggregate conjunction are derived packaging.
This file defines proposition targets and proves no faithfulness criterion.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace Langlands.Renard

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]

/-- Faithfulness compared with reflection of actual zero morphisms. -/
def FaithfulZeroMorphismCriterionStatement (F : C ⥤ D) [F.Additive] : Prop :=
  F.Faithful ↔
    (∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f = 0 → f = 0)

/-- Source sequence exactness and reflection of zero objects imply faithfulness. -/
def SequenceExactReflectsZeroFaithfulStatement
    (F : C ⥤ D) [F.Additive] : Prop :=
  SequenceExact F →
    (∀ X : C, IsZero (F.obj X) → IsZero X) →
      F.Faithful

/-- Aggregate proposition for the two faithfulness criteria. -/
def FaithfulnessCriteriaStatement (F : C ⥤ D) [F.Additive] : Prop :=
  FaithfulZeroMorphismCriterionStatement F ∧
    SequenceExactReflectsZeroFaithfulStatement F

end Langlands.Renard
