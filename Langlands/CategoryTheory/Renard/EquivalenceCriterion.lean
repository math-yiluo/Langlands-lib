import Langlands.CategoryTheory.Renard.EquivalenceCriterionStatements

/-!
# Renard A.II.2: the equivalence criterion

A fully faithful, essentially surjective functor admits an actual quasi-inverse
and both natural isomorphisms, by Mathlib's `Functor.asEquivalence` construction.

Implementation adapted from Worker 709's shared draft by Worker 1158.
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace Langlands.Renard

theorem equivalenceCriterion
    (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D] :
    EquivalenceCriterionStatement C D := by
  intro F hFull hFaithful hEssSurj
  let : F.Full := { map_surjective := fun {X Y} => hFull X Y }
  let : F.Faithful := { map_injective := fun {X Y} => hFaithful X Y }
  let : F.EssSurj := { mem_essImage := hEssSurj }
  let : F.IsEquivalence := {}
  exact ⟨F.asEquivalence.inverse,
    ⟨F.asEquivalence.unitIso.symm⟩, ⟨F.asEquivalence.counitIso⟩⟩

end Langlands.Renard
