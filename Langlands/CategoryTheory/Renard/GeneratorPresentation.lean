import Langlands.CategoryTheory.Renard.GeneratorPresentationStatements
import Mathlib.CategoryTheory.Generator.Preadditive

/-!
# Presentations by two coproducts of a generator

Faithfulness of Renard's integer-module Hom functor makes its source a separator.
Evaluation from the coproduct over all morphisms is therefore an epimorphism.
Applying evaluation again to its kernel gives the required right-exact row.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Renard's faithful Hom functor detects parallel morphisms. -/
theorem homGenerator_isSeparator {P : C} (hP : HomGenerator P) : IsSeparator P := by
  let : (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P).Faithful := hP
  exact (isSeparator_iff_faithful_preadditiveCoyonedaObj P).2
    (Functor.Faithful.of_comp (preadditiveCoyonedaObj P)
      (ModuleCat.restrictScalars (Int.castRingHom (End P)ᵐᵒᵖ)))

/-- Evaluation over all morphisms from a generator is an epimorphism. -/
theorem homGenerator_epi_evaluation [HasCoproducts.{v} C] {P : C}
    (hP : HomGenerator P) (M : C) :
    Epi (Sigma.desc fun a : P ⟶ M => a) :=
  (isSeparator_iff_epi P).1 (homGenerator_isSeparator hP) M

/-- Every object admits a right-exact presentation by two coproducts of copies
of a generator, with both indexing types in the Hom universe. -/
theorem generatorPresentation [HasCoproducts.{v} C] (P : C) :
    GeneratorPresentationStatement P := by
  intro hP M
  let g : (∐ fun _ : P ⟶ M => P) ⟶ M := Sigma.desc fun a : P ⟶ M => a
  let e : (∐ fun _ : P ⟶ kernel g => P) ⟶ kernel g :=
    Sigma.desc fun a : P ⟶ kernel g => a
  let f := e ≫ kernel.ι g
  have h : f ≫ g = 0 := by
    simp only [f, Category.assoc, kernel.condition, comp_zero]
  refine ⟨P ⟶ M, P ⟶ kernel g, f, g, h, ?_, homGenerator_epi_evaluation hP M⟩
  apply (ShortComplex.exact_iff_epi_kernel_lift (ShortComplex.mk f g h)).2
  have he : kernel.lift g f h = e := by
    apply (cancel_mono (kernel.ι g)).1
    simp only [kernel.lift_ι]
    rfl
  rw [he]
  exact homGenerator_epi_evaluation hP (kernel g)

end Langlands.Renard
