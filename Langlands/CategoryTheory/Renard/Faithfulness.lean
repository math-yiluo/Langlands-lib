import Langlands.CategoryTheory.Renard.FaithfulnessStatements
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Renard's faithfulness criteria

Zero-morphism reflection gives injectivity by applying additivity to a
difference. Sequence exactness preserves the actual image factorization,
so zero-object reflection gives zero-morphism reflection.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace Langlands.Renard

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- An additive functor is faithful exactly when it reflects zero morphisms. -/
theorem faithfulZeroMorphismCriterion : FaithfulZeroMorphismCriterionStatement F := by
  constructor
  · intro hF
    let : F.Faithful := hF
    intro X Y f hf
    exact F.zero_of_map_zero f hf
  · intro hF
    refine ⟨?_⟩
    intro X Y f g hfg
    apply sub_eq_zero.mp
    apply hF (f - g)
    simp only [F.map_sub, hfg, sub_self]

/-- Exactness and reflection of categorical zero objects imply faithfulness. -/
theorem sequenceExactReflectsZeroFaithful :
    SequenceExactReflectsZeroFaithfulStatement F := by
  intro hExact hReflect
  let : F.PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_preserves_shortExact_left F
      (fun S hS => hExact.1 S ⟨hS.exact, hS.mono_f⟩)
  let : F.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_preserves_shortExact_right F
      (fun S hS => hExact.2 S ⟨hS.exact, hS.epi_g⟩)
  apply (faithfulZeroMorphismCriterion F).2
  intro X Y f hf
  have hp : F.map (Abelian.factorThruImage f) = 0 :=
    zero_of_comp_mono (F.map (Abelian.image.ι f)) (by
      rw [← F.map_comp, Abelian.image.fac, hf])
  have hImage : IsZero (Abelian.image f) :=
    hReflect _ (IsZero.of_epi_eq_zero _ hp)
  rw [← Abelian.image.fac f, hImage.eq_zero_of_src (Abelian.image.ι f), comp_zero]

/-- The exact published aggregate of the two faithfulness criteria. -/
theorem faithfulnessCriteria : FaithfulnessCriteriaStatement F :=
  ⟨faithfulZeroMorphismCriterion F, sequenceExactReflectsZeroFaithful F⟩

end Langlands.Renard
