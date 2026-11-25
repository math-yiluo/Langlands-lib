/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition properties of morphism properties

The instance `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.iInf` shows that an
indexed intersection `⨅ i, W i` of morphism properties which all have the two-out-of-three
property again has it. The lemma `CategoryTheory.MorphismProperty.endAsHom_pow_mem` shows that a
multiplicative morphism property containing an endomorphism contains its powers.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category* C]

/-- An indexed intersection of morphism properties which have the two-out-of-three property
has the two-out-of-three property. -/
instance HasTwoOutOfThreeProperty.iInf {ι : Type*} {W : ι → MorphismProperty C}
    [∀ i, (W i).HasTwoOutOfThreeProperty] : (⨅ i, W i).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := by
    rw [iInf_iff] at hg hfg ⊢
    exact fun i ↦ (W i).of_postcomp f g (hg i) (hfg i)
  of_precomp f g hf hfg := by
    rw [iInf_iff] at hf hfg ⊢
    exact fun i ↦ (W i).of_precomp f g (hf i) (hfg i)


/-- A multiplicative morphism property containing an endomorphism contains its powers. -/
lemma endAsHom_pow_mem (P : MorphismProperty C) [P.IsMultiplicative] {Z : C} {Φ : Z ⟶ Z}
    (hΦ : P Φ) (m : ℕ) : P (End.asHom (End.of Φ ^ m)) := by
  induction m with
  | zero => exact P.id_mem Z
  | succ m ih =>
    rw [pow_succ, End.mul_asHom]
    exact P.comp_mem _ _ hΦ ih

end CategoryTheory.MorphismProperty
