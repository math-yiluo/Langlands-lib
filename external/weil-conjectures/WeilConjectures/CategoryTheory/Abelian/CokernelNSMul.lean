/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Cokernels of multiplication by an integer

Let `C` be a preadditive category and `n` a natural number. This file collects ways to
recognise a cokernel of the multiplication `n • 𝟙 X : X ⟶ X`:

- `CategoryTheory.Limits.CokernelCofork.isColimitOfArrowIso`: a cokernel can be transported
  along an isomorphism of arrows.
- `CategoryTheory.Limits.CokernelCofork.isColimitOfEq`: a cokernel of `f` is a cokernel of any
  `f'` equal to `f`.
- `CategoryTheory.Functor.isColimitCokernelCoforkNSMulMap`: a functor which preserves the
  cokernel of `n • 𝟙 X` maps it to a cokernel of `n • 𝟙 (G.obj X)`.
- `CategoryTheory.ShortComplex.ShortExact.isColimitCokernelCoforkNSMul`: for a short exact
  sequence `0 ⟶ A ⟶ B ⟶ D ⟶ 0` on which `n` is an epimorphism of `A`, the cokernel of `n` on
  `B` is the cokernel of `n` on `D` (the relevant part of the snake lemma).
- `CategoryTheory.Limits.Cofan.IsColimit.isColimitCokernelCoforkNSMul`: the cokernel of `n` on
  a coproduct is the coproduct of the cokernels of `n`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C]

namespace Limits.CokernelCofork

variable [HasZeroMorphisms C]

/-- The factorisation through a cokernel `π`, as an equation involving `π` itself. -/
@[reassoc (attr := simp)]
lemma π_desc' {X Y Q W : C} {f : X ⟶ Y} {π : Y ⟶ Q} {w : f ≫ π = 0}
    (h : IsColimit (CokernelCofork.ofπ π w)) (k : Y ⟶ W) (hk : f ≫ k = 0) :
    π ≫ (CokernelCofork.IsColimit.desc' h k hk).1 = k :=
  (CokernelCofork.IsColimit.desc' h k hk).2

/-- A cokernel of `f` is a cokernel of any morphism equal to `f`. -/
def isColimitOfEq {X Y Q : C} {f f' : X ⟶ Y} (hf : f = f') {π : Y ⟶ Q} {w : f ≫ π = 0}
    (h : IsColimit (CokernelCofork.ofπ π w)) :
    IsColimit (CokernelCofork.ofπ (f := f') π (hf ▸ w)) := by
  subst hf
  exact h

/-- A cokernel can be transported along an isomorphism of arrows: if `π` is a cokernel of
`f : X ⟶ Y` and `f'` is identified with `f` by isomorphisms `e₁ : X' ≅ X` and `e₂ : Y' ≅ Y`,
then `e₂.hom ≫ π` is a cokernel of `f'`. -/
def isColimitOfArrowIso {X Y X' Y' Q : C} {f : X ⟶ Y} {f' : X' ⟶ Y'} (e₁ : X' ≅ X)
    (e₂ : Y' ≅ Y) (comm : f' ≫ e₂.hom = e₁.hom ≫ f) {π : Y ⟶ Q} {w : f ≫ π = 0}
    (h : IsColimit (CokernelCofork.ofπ π w)) :
    IsColimit (CokernelCofork.ofπ (f := f') (e₂.hom ≫ π)
      (by rw [reassoc_of% comm, w, Limits.comp_zero])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun g hg ↦ (CokernelCofork.IsColimit.desc' h (e₂.inv ≫ g) (by
      rw [← cancel_epi e₁.hom, Limits.comp_zero, ← Category.assoc, ← comm, Category.assoc,
        Iso.hom_inv_id_assoc, hg])).1)
    (fun g hg ↦ by
      rw [Category.assoc, CokernelCofork.π_desc' h _ _, Iso.hom_inv_id_assoc])
    (fun g hg m hm ↦ by
      refine Cofork.IsColimit.hom_ext h ?_
      change π ≫ m = π ≫ _
      rw [CokernelCofork.π_desc' h _ _, ← hm, Category.assoc, Iso.inv_hom_id_assoc])

end Limits.CokernelCofork

/-- Being a colimit cofan is stable under reindexing along an equivalence of index types. This
is `CategoryTheory.Limits.Cofan.isColimitEquivOfEquiv` without its (unused) assumptions that the
coproducts exist. -/
def Limits.Cofan.isColimitReindex {α β : Type*} {f : α → C} (ε : β ≃ α) {c : Cofan f}
    (hc : IsColimit c) : IsColimit (Cofan.mk c.pt fun b ↦ c.inj (ε b) : Cofan (f ∘ ε)) :=
  IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence ε) hc

section Preadditive

variable [Preadditive C] (n : ℕ)

/-- Multiplication by `n` commutes with every morphism. -/
@[reassoc]
lemma nsmul_id_comp_eq_comp_nsmul_id {X Y : C} (f : X ⟶ Y) :
    (n • 𝟙 X) ≫ f = f ≫ (n • 𝟙 Y) := by
  rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

/-- A cokernel of multiplication by `n` can be transported along an isomorphism. -/
def Limits.CokernelCofork.isColimitNSMulOfIso {X X' Q : C} (e : X' ≅ X) {π : X ⟶ Q}
    {w : (n • 𝟙 X) ≫ π = 0} (h : IsColimit (CokernelCofork.ofπ π w)) :
    IsColimit (CokernelCofork.ofπ (f := n • 𝟙 X') (e.hom ≫ π)
      (by rw [nsmul_id_comp_eq_comp_nsmul_id_assoc, w, Limits.comp_zero])) :=
  CokernelCofork.isColimitOfArrowIso e e (nsmul_id_comp_eq_comp_nsmul_id n e.hom) h

variable {D : Type*} [Category* D] [Preadditive D]

/-- A functor which preserves the cokernel of multiplication by `n` on `X` maps it to a
cokernel of multiplication by `n` on `G.obj X`. -/
def Functor.isColimitCokernelCoforkNSMulMap (G : C ⥤ D) [G.Additive] {X Q : C} {π : X ⟶ Q}
    {w : (n • 𝟙 X) ≫ π = 0} (h : IsColimit (CokernelCofork.ofπ π w))
    [PreservesColimit (parallelPair (n • 𝟙 X) 0) G] :
    IsColimit (CokernelCofork.ofπ (f := n • 𝟙 (G.obj X)) (G.map π)
      (by rw [← G.map_id, ← G.map_nsmul, ← G.map_comp, w, G.map_zero])) :=
  CokernelCofork.isColimitOfEq (by rw [G.map_nsmul, G.map_id])
    ((isColimitMapCoconeCoforkEquiv' G w) (isColimitOfPreserves G h))

/-- **Cokernels of multiplication by `n` along a short exact sequence.** Let
`0 ⟶ A ⟶ B ⟶ D ⟶ 0` be a short exact sequence on which multiplication by `n` is an
epimorphism of `A`. If `π` is a cokernel of `n` on `D`, then `B ⟶ D ⟶ Q` is a cokernel of `n`
on `B`. This is the part of the snake lemma for multiplication by `n` which identifies the two
cokernels. -/
def ShortComplex.ShortExact.isColimitCokernelCoforkNSMul [Balanced C] {S : ShortComplex C}
    (hS : S.ShortExact) [Epi (n • 𝟙 S.X₁)] {Q : C} {π : S.X₃ ⟶ Q}
    {w : (n • 𝟙 S.X₃) ≫ π = 0} (h : IsColimit (CokernelCofork.ofπ π w)) :
    IsColimit (CokernelCofork.ofπ (f := n • 𝟙 S.X₂) (S.g ≫ π)
      (by rw [nsmul_id_comp_eq_comp_nsmul_id_assoc, w, Limits.comp_zero])) :=
  have := hS.epi_g
  CokernelCofork.IsColimit.ofπ _ _
    (fun g hg ↦ (CokernelCofork.IsColimit.desc' h
      (CokernelCofork.IsColimit.desc' hS.gIsCokernel g (by
        rw [← cancel_epi (n • 𝟙 S.X₁), Limits.comp_zero,
          nsmul_id_comp_eq_comp_nsmul_id_assoc, hg, Limits.comp_zero])).1 (by
        rw [← cancel_epi S.g, Limits.comp_zero, ← nsmul_id_comp_eq_comp_nsmul_id_assoc,
          CokernelCofork.π_desc' hS.gIsCokernel g _, hg])).1)
    (fun g hg ↦ by
      rw [Category.assoc, CokernelCofork.π_desc' h _ _,
        CokernelCofork.π_desc' hS.gIsCokernel g _])
    (fun g hg m hm ↦ by
      refine Cofork.IsColimit.hom_ext h ?_
      change π ≫ m = π ≫ _
      rw [CokernelCofork.π_desc' h _ _, ← cancel_epi S.g,
        CokernelCofork.π_desc' hS.gIsCokernel g _, ← hm, Category.assoc])

/-- **Cokernels of multiplication by `n` commute with coproducts.** Let `cA` be a coproduct of
a family `A`, `cQ` a coproduct of a family `Q`, and for each `i` let `π i : A i ⟶ Q i` be a
cokernel of multiplication by `n`. Then the induced map `∐ A ⟶ ∐ Q` is a cokernel of
multiplication by `n` on `∐ A`. -/
def Limits.Cofan.IsColimit.isColimitCokernelCoforkNSMul {ι : Type*} {A Q : ι → C}
    {cA : Cofan A} (hA : IsColimit cA) {cQ : Cofan Q} (hQ : IsColimit cQ)
    (π : ∀ i, A i ⟶ Q i) (w : ∀ i, (n • 𝟙 (A i)) ≫ π i = 0)
    (h : ∀ i, IsColimit (CokernelCofork.ofπ (π i) (w i))) :
    IsColimit (CokernelCofork.ofπ (f := n • 𝟙 cA.pt)
      (Cofan.IsColimit.desc hA fun i ↦ π i ≫ cQ.inj i) (by
        refine Cofan.IsColimit.hom_ext hA _ _ fun i ↦ ?_
        rw [Limits.comp_zero, ← nsmul_id_comp_eq_comp_nsmul_id_assoc,
          Cofan.IsColimit.fac, ← Category.assoc, w, Limits.zero_comp])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun g hg ↦ Cofan.IsColimit.desc hQ fun i ↦ (CokernelCofork.IsColimit.desc' (h i)
      (cA.inj i ≫ g) (by rw [nsmul_id_comp_eq_comp_nsmul_id_assoc, hg, Limits.comp_zero])).1)
    (fun g hg ↦ by
      refine Cofan.IsColimit.hom_ext hA _ _ fun i ↦ ?_
      rw [Cofan.IsColimit.fac_assoc, Category.assoc, Cofan.IsColimit.fac,
        CokernelCofork.π_desc' (h i) _ _])
    (fun g hg m hm ↦ by
      refine Cofan.IsColimit.hom_ext hQ _ _ fun i ↦ ?_
      rw [Cofan.IsColimit.fac]
      refine Cofork.IsColimit.hom_ext (h i) ?_
      change π i ≫ _ = π i ≫ _
      rw [CokernelCofork.π_desc' (h i) _ _, ← hm, Cofan.IsColimit.fac_assoc,
        Category.assoc])

end Preadditive

end CategoryTheory

end
