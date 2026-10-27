import Langlands.CategoryTheory.Picard.TensorEquivalenceProof
import Langlands.CategoryTheory.Picard.UnitTensorCancellationStatement
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Proof of cancellation for a tensor of morphisms from the unit
-/

universe v u

open CategoryTheory MonoidalCategory

namespace Langlands.CategoryTheory.Picard

/-- In a braided monoidal category, if the tensor of two morphisms from the
unit is an isomorphism, then its left factor is an isomorphism. -/
theorem isIso_left_of_isIso_unitTensorHom
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {M N : C} (s : 𝟙_ C ⟶ M) (t : 𝟙_ C ⟶ N) [IsIso (s ⊗ₘ t)] : IsIso s := by
  -- The inverse of `s ⊗ₘ t` and braiding make `M` a right tensor inverse of `N`.
  let e : N ⊗ M ≅ 𝟙_ C := β_ N M ≪≫ (asIso (s ⊗ₘ t)).symm ≪≫ λ_ (𝟙_ C)
  have hN : (tensorLeft N).IsEquivalence :=
    (tensorInvertibilityEquivalence C N).1 ⟨M, ⟨e⟩⟩
  -- The factorization `s ⊗ₘ t = s ▷ 𝟙_ C ≫ M ◁ t` gives a retraction of `s`.
  have hmono : IsSplitMono s := by
    refine IsSplitMono.mk' ⟨(ρ_ M).inv ≫ M ◁ t ≫ inv (s ⊗ₘ t) ≫ (ρ_ (𝟙_ C)).hom, ?_⟩
    rw [rightUnitor_inv_naturality_assoc, ← Category.assoc (s ▷ 𝟙_ C),
      ← tensorHom_def, IsIso.hom_inv_id_assoc, Iso.inv_hom_id]
  -- The factorization `s ⊗ₘ t = 𝟙_ C ◁ t ≫ s ▷ N` makes `s ▷ N` an epimorphism.
  have hright : Epi (s ▷ N) := by
    have : Epi (𝟙_ C ◁ t ≫ s ▷ N) := by
      rw [← tensorHom_def']
      infer_instance
    exact epi_of_epi (𝟙_ C ◁ t) (s ▷ N)
  -- Braiding turns `s ▷ N` into `N ◁ s`, and `tensorLeft N` reflects epimorphisms.
  have hleft : Epi ((tensorLeft N).map s) := by
    have : (tensorLeft N).map s = ((β_ N (𝟙_ C)).hom ≫ s ▷ N) ≫ (β_ N M).inv :=
      (Iso.eq_comp_inv _).2 (BraidedCategory.braiding_naturality_right N s)
    rw [this]
    infer_instance
  have hepi : Epi s := (tensorLeft N).epi_of_epi_map hleft
  exact isIso_of_epi_of_isSplitMono s

/-- In a braided monoidal category, if the tensor of two morphisms from the
unit is an isomorphism, then both morphisms are isomorphisms. -/
theorem unitTensorCancellation
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] :
    UnitTensorCancellationStatement C := by
  intro M N s t h
  refine ⟨isIso_left_of_isIso_unitTensorHom s t, ?_⟩
  -- Naturality of the braiding exchanges the two factors.
  have : IsIso (t ⊗ₘ s) := by
    have hts : t ⊗ₘ s = (β_ (𝟙_ C) (𝟙_ C)).inv ≫ (s ⊗ₘ t) ≫ (β_ M N).hom := by
      rw [BraidedCategory.braiding_naturality, Iso.inv_hom_id_assoc]
    rw [hts]
    infer_instance
  exact isIso_left_of_isIso_unitTensorHom t s

end Langlands.CategoryTheory.Picard
