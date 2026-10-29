import Langlands.CategoryTheory.Renard.HomGeneratorCriteriaStatements
import Langlands.CategoryTheory.Renard.Faithfulness

/-!
# Renard's generator comparisons and projective nonzero-Hom criterion

Faithfulness of the integer-module Hom functors is equivalent to faithfulness
after forgetting to additive groups. The projective criterion uses the published
exact-functor zero-object reflection lemma.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.CategoryTheory.Renard

universe v u

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Renard generation agrees with the native separator predicate. -/
theorem homGeneratorComparison (P : C) : HomGeneratorComparisonStatement P := by
  change (preadditiveCoyonedaInt P).Faithful ↔ IsSeparator P
  rw [isSeparator_iff_faithful_preadditiveCoyoneda,
    ← preadditiveCoyonedaInt_comp_forget₂ P]
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    let := h
    exact Functor.Faithful.of_comp _ (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v})

/-- Renard cogeneration agrees with the native coseparator predicate. -/
theorem homCogeneratorComparison (P : C) : HomCogeneratorComparisonStatement P := by
  change (preadditiveYonedaInt P).Faithful ↔ IsCoseparator P
  rw [isCoseparator_iff_faithful_preadditiveYoneda,
    ← preadditiveYonedaInt_comp_forget₂ P]
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    let := h
    exact Functor.Faithful.of_comp _ (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v})

/-- A projective object generates exactly when it maps nontrivially to each
nonzero object. -/
theorem projectiveProgeneratorCriterion (P : C) :
    ProjectiveProgeneratorCriterionStatement P := by
  intro hProjective
  constructor
  · intro hProgenerator Y hY
    classical
    by_contra hNo
    have hAll : ∀ f : P ⟶ Y, f = 0 := by
      simpa only [not_exists, not_not] using hNo
    apply hY
    apply (IsZero.iff_id_eq_zero Y).2
    apply ((homGeneratorComparison P).mp hProgenerator.2).def (𝟙 Y) 0
    intro f
    simpa only [Category.comp_id, comp_zero] using hAll f
  · intro hNonzero
    refine ⟨hProjective, ?_⟩
    change (preadditiveCoyonedaInt P).Faithful
    apply sequenceExactReflectsZeroFaithful (preadditiveCoyonedaInt P) hProjective
    intro Y hY
    classical
    by_contra hnY
    obtain ⟨f, hf⟩ := hNonzero Y hnY
    have hSub : Subsingleton (P ⟶ Y) :=
      ModuleCat.subsingleton_of_isZero hY
    exact hf (hSub.elim f 0)

/-- The exact published aggregate, with no additional hypotheses. -/
theorem homGeneratorCriteria (P : C) : HomGeneratorCriteriaStatement P :=
  ⟨homGeneratorComparison P, homCogeneratorComparison P,
    projectiveProgeneratorCriterion P⟩

end Langlands.Renard
