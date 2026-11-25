/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Copowers along an injection of index types

In a category with zero morphisms, an injection `f : ι → ι'` induces a split monomorphism
between the copowers `∐ (fun (_ : ι) ↦ X) ⟶ ∐ (fun (_ : ι') ↦ X)` of an object `X`: the
retraction sends the summand indexed by `s : ι'` to the summand indexed by the (unique)
antecedent of `s`, if there is one, and to zero otherwise.

A product all of whose factors but one are zero is that factor
(`CategoryTheory.Limits.Pi.isoOfIsZero`).
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The morphism between copowers of `X : C` induced by an injection `f : ι → ι'` of index
types is a split monomorphism. -/
lemma isSplitMono_sigmaDesc_of_injective (X : C) {ι ι' : Type*} (f : ι → ι')
    (hf : Function.Injective f) [HasCoproduct (fun (_ : ι) ↦ X)]
    [HasCoproduct (fun (_ : ι') ↦ X)] :
    IsSplitMono (Sigma.desc (fun (i : ι) ↦ Sigma.ι (fun (_ : ι') ↦ X) (f i))) := by
  classical
  refine ⟨⟨Sigma.desc
    (fun s ↦ if h : ∃ i, f i = s then Sigma.ι (fun (_ : ι) ↦ X) h.choose else 0), ?_⟩⟩
  ext i
  have h : ∃ j, f j = f i := ⟨i, rfl⟩
  rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc, dite_eq_left h, hf h.choose_spec,
    Category.comp_id]

/-- If `f : ι → ι'` is injective, then the copower `∐ (fun (_ : ι') ↦ X)` admits an
epimorphism onto the copower `∐ (fun (_ : ι) ↦ X)`. -/
lemma exists_epi_copower_of_injective (X : C) {ι ι' : Type*} (f : ι → ι')
    (hf : Function.Injective f) [HasCoproduct (fun (_ : ι) ↦ X)]
    [HasCoproduct (fun (_ : ι') ↦ X)] :
    ∃ (r : (∐ fun (_ : ι') ↦ X) ⟶ (∐ fun (_ : ι) ↦ X)), Epi r := by
  have := isSplitMono_sigmaDesc_of_injective X f hf
  refine ⟨retraction (Sigma.desc (fun (i : ι) ↦ Sigma.ι (fun (_ : ι') ↦ X) (f i))), ?_⟩
  have : IsSplitEpi (retraction (Sigma.desc
    (fun (i : ι) ↦ Sigma.ι (fun (_ : ι') ↦ X) (f i)))) := ⟨⟨_, IsSplitMono.id _⟩⟩
  infer_instance

/-- A product `∏ᶜ F` all of whose factors `F j` with `j ≠ j₀` are zero is isomorphic to the
factor `F j₀`, through the projection `Pi.π F j₀`. -/
@[simps hom]
noncomputable def Pi.isoOfIsZero {J : Type*} [DecidableEq J] (F : J → C) [HasProduct F] (j₀ : J)
    (hF : ∀ j, j ≠ j₀ → IsZero (F j)) : ∏ᶜ F ≅ F j₀ where
  hom := Pi.π F j₀
  inv := Pi.lift fun j ↦ if h : j = j₀ then eqToHom (by rw [h]) else 0
  hom_inv_id := by
    refine Pi.hom_ext _ _ fun j ↦ ?_
    by_cases h : j = j₀
    · subst h
      simp
    · exact (hF j h).eq_of_tgt _ _
  inv_hom_id := by simp

end CategoryTheory.Limits
