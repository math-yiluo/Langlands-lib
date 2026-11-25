/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCouple
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-!
# Kernel and image identities for an exact-couple differential

Source: Stacks Project, Lemma 12.21.2 and Remark 12.21.5 (Tags 011R and 0AMJ).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

private theorem pullback_kernelSubobject
    {C : Type u} [Category.{v} C] [Abelian C] {A B T : C}
    (f : A ⟶ B) (g : B ⟶ T) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g) := by
  apply le_antisymm
  · apply Subobject.le_of_factors
    apply kernelSubobject_factors
    have hw := (Subobject.isPullback f (kernelSubobject g)).w
    rw [← Category.assoc, ← hw, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  · apply Subobject.le_of_factors
    apply pullback_factors
    apply kernelSubobject_factors
    rw [Category.assoc, kernelSubobject_arrow_comp]

/-- Kernel and image identities for the differential of an exact couple.
Source: Stacks Project, Lemma 12.21.2, clauses (1)--(2), and Remark 12.21.5
(Tags 011R and 0AMJ) (blueprint: lem-sp-derived-couple-kernel-identities).

Proof. The kernel of a composite is the pullback of the second map's kernel:
both inclusions follow from the kernel and pullback universal properties.
Reindex `exact_g` to identify that kernel with the incoming alpha image.
Factor `f` through its image; its first factor is epi, so precomposing by it
does not change the image after postcomposition with `g`. Substitute
`exact_alpha` for the other image formula. Finally, the kernel condition for
`d = f ≫ g` makes the cycle restriction of `f` factor through `ker g`, giving
the last image inequality. -/
theorem derived_couple_kernel_identities {C : Type u} [Category.{v} C] [Abelian C]
    {s : ℕ} (X : BigradedExactCouple C s) :
    ∀ p q : ℤ,
      let a : X.D (p + 3) (q - 2) ⟶ X.D (p + 2) (q - 1) :=
        X.alpha (p + 3) (q - 2) ≫ eqToHom (by congr 1 <;> omega)
      kernelSubobject (X.d p q) =
          (Subobject.pullback (X.f p q)).obj (kernelSubobject (X.g (p + 2) (q - 1))) ∧
      kernelSubobject (X.d p q) =
          (Subobject.pullback (X.f p q)).obj (imageSubobject a) ∧
      kernelSubobject (X.g (p + 2) (q - 1)) = imageSubobject a ∧
      imageSubobject (X.d p q) =
          imageSubobject ((imageSubobject (X.f p q)).arrow ≫ X.g (p + 2) (q - 1)) ∧
      imageSubobject (X.d p q) =
          imageSubobject ((kernelSubobject (X.alpha (p + 2) (q - 1))).arrow ≫
            X.g (p + 2) (q - 1)) ∧
      imageSubobject (X.f p q) = kernelSubobject (X.alpha (p + 2) (q - 1)) ∧
      imageSubobject (kernel.ι (X.d p q) ≫ X.f p q) ≤ imageSubobject a := by
  intro p q
  dsimp only
  have transport (r t p' q' : ℤ) (hp : r - 1 = p') (hq : t + 1 = q') :
      imageSubobject (X.alpha r t ≫ eqToHom (congrArg₂ X.D hp hq)) =
        kernelSubobject (X.g p' q') := by
    subst p'
    subst q'
    simpa using X.exact_g r t
  have hg := (transport (p + 3) (q - 2) (p + 2) (q - 1)
    (by omega) (by omega)).symm
  have hk : kernelSubobject (X.d p q) =
      (Subobject.pullback (X.f p q)).obj (kernelSubobject (X.g (p + 2) (q - 1))) :=
    (pullback_kernelSubobject _ _).symm
  have hi : imageSubobject (X.d p q) =
      imageSubobject ((imageSubobject (X.f p q)).arrow ≫ X.g (p + 2) (q - 1)) := by
    calc
      _ = imageSubobject (factorThruImageSubobject (X.f p q) ≫
          ((imageSubobject (X.f p q)).arrow ≫ X.g (p + 2) (q - 1))) := by
        rw [← Category.assoc, imageSubobject_arrow_comp]
        rfl
      _ = _ := imageSubobject_comp_of_epi _ _
  refine ⟨hk, hk.trans (by rw [hg]), hg, hi, ?_, X.exact_alpha p q, ?_⟩
  · rw [← X.exact_alpha p q]
    exact hi
  · rw [← hg]
    have hz : (kernel.ι (X.d p q) ≫ X.f p q) ≫ X.g (p + 2) (q - 1) = 0 := by
      rw [Category.assoc]
      exact kernel.condition (X.d p q)
    exact imageSubobject_le _ (factorThruKernelSubobject _ _ hz)
      (factorThruKernelSubobject_comp_arrow _ _ hz)
end CategoryTheory.BigradedExactCouple
