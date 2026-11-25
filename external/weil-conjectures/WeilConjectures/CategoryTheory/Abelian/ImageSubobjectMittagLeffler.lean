/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Order.Category.Preord

/-!
# Comparing images, and the Mittag-Leffler condition for towers

In an abelian category, the image of `f : A ⟶ B` is contained in the image of `g : A' ⟶ B` if
and only if `f` composed with the cokernel of `g` vanishes
(`CategoryTheory.Abelian.imageSubobject_le_imageSubobject_iff`). Consequently such inclusions are
preserved by postcomposition (`CategoryTheory.Abelian.imageSubobject_comp_le_imageSubobject_comp`)
and by functors preserving cokernels
(`CategoryTheory.Abelian.imageSubobject_map_le_imageSubobject_map`).

We apply this to the Mittag-Leffler condition for a tower `T : ℕᵒᵖ ⥤ C`, in the form
"for every `n` there is `N ≥ n` such that the image of `T_N ⟶ Tₙ` is contained in the image of
`T_k ⟶ Tₙ` for every `k ≥ n`": it is invariant under isomorphism of towers
(`CategoryTheory.Abelian.mittagLeffler_imageSubobject_of_iso`) and preserved by right exact
functors (`CategoryTheory.Abelian.mittagLeffler_imageSubobject_comp`). Finally a diagram whose
objects lie in the essential image of a fully faithful functor lifts along it
(`CategoryTheory.Functor.FullyFaithful.liftDiagram`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

namespace Functor.FullyFaithful

variable {C D J : Type*} [Category* C] [Category* D] [Category* J] {F : C ⥤ D}
  (hF : F.FullyFaithful) (T : J ⥤ D) (X : J → C) (e : ∀ j, F.obj (X j) ≅ T.obj j)

/-- A diagram `T` in `D` whose objects are identified with the images `F (X j)` under a fully
faithful functor `F` lifts to a diagram in `C` with objects `X j`. -/
@[simps]
noncomputable def liftDiagram : J ⥤ C where
  obj := X
  map f := hF.preimage ((e _).hom ≫ T.map f ≫ (e _).inv)
  map_id j := hF.map_injective (by simp)
  map_comp f g := hF.map_injective (by simp)

/-- The lift of a diagram along a fully faithful functor `F` recovers the diagram after
composing with `F`. -/
noncomputable def liftDiagramCompIso : hF.liftDiagram T X e ⋙ F ≅ T :=
  NatIso.ofComponents e (fun f ↦ by simp)

end Functor.FullyFaithful

namespace Abelian

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- In an abelian category, the image of `f` is contained in the image of `g` if and only if `f`
vanishes when composed with the cokernel of `g`. -/
theorem imageSubobject_le_imageSubobject_iff {A A' B : C} (f : A ⟶ B) (g : A' ⟶ B) :
    imageSubobject f ≤ imageSubobject g ↔ f ≫ cokernel.π g = 0 := by
  constructor
  · intro h
    rw [← imageSubobject_arrow_comp f, ← Subobject.ofLE_arrow h, Category.assoc, Category.assoc,
      imageSubobject_arrow_comp_eq_zero (cokernel.condition g), comp_zero, comp_zero]
  · intro h
    have hS : (ShortComplex.mk g (cokernel.π g) (cokernel.condition g)).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel g)
    rw [ShortComplex.exact_iff_image_eq_kernel] at hS
    rw [hS]
    exact le_kernelSubobject _ _ (imageSubobject_arrow_comp_eq_zero h)

/-- An inclusion of images `im f ≤ im g` is preserved by postcomposition with any morphism. -/
theorem imageSubobject_comp_le_imageSubobject_comp {A A' B B' : C} {f : A ⟶ B} {g : A' ⟶ B}
    (h : imageSubobject f ≤ imageSubobject g) (e : B ⟶ B') :
    imageSubobject (f ≫ e) ≤ imageSubobject (g ≫ e) := by
  rw [imageSubobject_le_imageSubobject_iff] at h ⊢
  rw [Category.assoc, ← cokernel.π_desc g (e ≫ cokernel.π (g ≫ e))
    (by rw [← Category.assoc, cokernel.condition]), ← Category.assoc, h, zero_comp]

/-- An inclusion of images `im f ≤ im g` is preserved by a functor preserving finite
colimits. -/
theorem imageSubobject_map_le_imageSubobject_map (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteColimits F] {A A' B : C} {f : A ⟶ B} {g : A' ⟶ B}
    (h : imageSubobject f ≤ imageSubobject g) :
    imageSubobject (F.map f) ≤ imageSubobject (F.map g) := by
  rw [imageSubobject_le_imageSubobject_iff] at h ⊢
  rw [← cancel_mono (cokernelComparison g F), Category.assoc, π_comp_cokernelComparison,
    ← F.map_comp, h, F.map_zero, zero_comp]

/-- **The Mittag-Leffler condition is invariant under isomorphism of towers**: if for every `n`
there is `N ≥ n` such that the image of `T_N ⟶ Tₙ` is contained in the image of every
`T_k ⟶ Tₙ`, `k ≥ n`, the same holds for a tower isomorphic to `T`. -/
theorem mittagLeffler_imageSubobject_of_iso {T T' : ℕᵒᵖ ⥤ C} (α : T ≅ T')
    (h : ∀ n : ℕ, ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      imageSubobject (T.map (homOfLE hN).op) ≤ imageSubobject (T.map (homOfLE hk).op))
    (n : ℕ) : ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      imageSubobject (T'.map (homOfLE hN).op) ≤ imageSubobject (T'.map (homOfLE hk).op) := by
  obtain ⟨N, hN, hk⟩ := h n
  refine ⟨N, hN, fun k hk' ↦ ?_⟩
  have e (m : ℕ) (hm : n ≤ m) :
      T'.map (homOfLE hm).op = α.inv.app _ ≫ T.map (homOfLE hm).op ≫ α.hom.app _ := by
    simp
  rw [e N hN, e k hk', imageSubobject_iso_comp (α.inv.app _),
    imageSubobject_iso_comp (α.inv.app _)]
  exact imageSubobject_comp_le_imageSubobject_comp (hk k hk') _

/-- **Right exact functors preserve the Mittag-Leffler condition** (in its image form). -/
theorem mittagLeffler_imageSubobject_comp (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteColimits F] {T : ℕᵒᵖ ⥤ C}
    (h : ∀ n : ℕ, ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      imageSubobject (T.map (homOfLE hN).op) ≤ imageSubobject (T.map (homOfLE hk).op))
    (n : ℕ) : ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      imageSubobject ((T ⋙ F).map (homOfLE hN).op) ≤
        imageSubobject ((T ⋙ F).map (homOfLE hk).op) := by
  obtain ⟨N, hN, hk⟩ := h n
  exact ⟨N, hN, fun k hk' ↦ imageSubobject_map_le_imageSubobject_map F (hk k hk')⟩

end Abelian

end CategoryTheory
