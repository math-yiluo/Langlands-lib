import Langlands.CategoryTheory.Renard.HomExactnessComparisonStatements
import Langlands.CategoryTheory.Renard.FinitePreservation
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# Hom left exactness and projective/injective comparisons

The integer-module Hom functors preserve finite limits by reflection through
their group-valued comparisons. For a left exact additive functor, exactness
is equivalent to preservation of epimorphisms.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Langlands.Renard

private theorem sequenceExact_iff_preservesEpimorphisms
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] (hleft : SequenceLeftExact F) :
    SequenceExact F ↔ F.PreservesEpimorphisms := by
  constructor
  · intro h
    exact Functor.preservesEpimorphisms_of_preserves_shortExact_right F
      (fun S hS => h.2 S ⟨hS.exact, hS.epi_g⟩)
  · intro h
    let := h
    refine ⟨hleft, (Functor.preservesFiniteColimits_tfae F).out 1 2 |>.mp ?_⟩
    intro S hS
    let := hS.epi_g
    exact ⟨(hleft S ⟨hS.exact, hS.mono_f⟩).1, inferInstance⟩

private theorem preservesEpimorphisms_iff_comp_forget
    {A : Type*} [Category* A] (F : A ⥤ ModuleCat.{v} ℤ) :
    F.PreservesEpimorphisms ↔
      (F ⋙ forget (ModuleCat.{v} ℤ)).PreservesEpimorphisms := by
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    let := h
    exact Functor.preservesEpimorphisms_of_preserves_of_reflects F (forget _)

variable {C : Type u} [Category.{v} C] [Abelian C] (P : C)

/-- The actual covariant integer-module Hom functor is left sequence exact. -/
theorem covariantHomLeftExact : CovariantHomLeftExactStatement P := by
  let F := Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P
  let U := forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}
  have : PreservesFiniteLimits (F ⋙ U) := by
    change PreservesFiniteLimits
      (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P ⋙
        forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v})
    rw [Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt_comp_forget₂]
    infer_instance
  have : PreservesFiniteLimits F :=
    preservesFiniteLimits_of_reflects_of_preserves F U
  exact (sequenceLeftExactFiniteLimits F).mpr inferInstance

/-- The actual integer-module Hom functor on the opposite is left sequence exact. -/
theorem contravariantHomLeftExact : ContravariantHomLeftExactStatement P := by
  let F := Langlands.CategoryTheory.Renard.preadditiveYonedaInt P
  let U := forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}
  have : PreservesFiniteLimits (F ⋙ U) := by
    change PreservesFiniteLimits
      (Langlands.CategoryTheory.Renard.preadditiveYonedaInt P ⋙
        forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v})
    rw [Langlands.CategoryTheory.Renard.preadditiveYonedaInt_comp_forget₂]
    infer_instance
  have : PreservesFiniteLimits F :=
    preservesFiniteLimits_of_reflects_of_preserves F U
  exact (sequenceLeftExactFiniteLimits F).mpr inferInstance

/-- Renard's exact-Hom projectivity is Mathlib's projective lifting class. -/
theorem homProjectiveComparison : HomProjectiveComparisonStatement P := by
  change SequenceExact (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P) ↔
    CategoryTheory.Projective P
  rw [sequenceExact_iff_preservesEpimorphisms _ (covariantHomLeftExact P)]
  exact (preservesEpimorphisms_iff_comp_forget _).trans
    (Projective.projective_iff_preservesEpimorphisms_coyoneda_obj P).symm

/-- Renard's exact-Hom injectivity is Mathlib's injective extension class. -/
theorem homInjectiveComparison : HomInjectiveComparisonStatement P := by
  change SequenceExact (Langlands.CategoryTheory.Renard.preadditiveYonedaInt P) ↔
    CategoryTheory.Injective P
  rw [sequenceExact_iff_preservesEpimorphisms _ (contravariantHomLeftExact P)]
  exact (preservesEpimorphisms_iff_comp_forget _).trans
    (Injective.injective_iff_preservesEpimorphisms_yoneda_obj P).symm

/-- The exact published aggregate, with no object-property premise. -/
theorem homExactnessComparison : HomExactnessComparisonStatement P :=
  ⟨covariantHomLeftExact P, contravariantHomLeftExact P,
    homProjectiveComparison P, homInjectiveComparison P⟩

end Langlands.Renard
