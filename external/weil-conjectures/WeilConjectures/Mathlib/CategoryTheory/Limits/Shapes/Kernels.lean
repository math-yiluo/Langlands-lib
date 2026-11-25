/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Cokernels of maps between coproducts

## Main definitions

- `CategoryTheory.Limits.isColimitCokernelCoforkSigmaMap`: a coproduct of cokernels is a
  cokernel.
-/

@[expose] public section

namespace CategoryTheory.Limits

/-- A coproduct of cokernels is a cokernel: if each `g i : B i ⟶ Z i` is a cokernel of
`f i : A i ⟶ B i`, then `Sigma.map g` is a cokernel of `Sigma.map f`:
```
  ∐ A ──Sigma.map f──▶ ∐ B ──Sigma.map g──▶ ∐ Z
   ▲                    ▲                    ▲
   │ ι i                │ ι i                │ ι i
  A i ───────f i──────▶ B i ──────g i──────▶ Z i
```
-/
noncomputable def isColimitCokernelCoforkSigmaMap {C : Type*} [Category C] [HasZeroMorphisms C]
    {ι : Type*} {A B Z : ι → C} [HasCoproduct A] [HasCoproduct B] [HasCoproduct Z]
    (f : ∀ i, A i ⟶ B i) (g : ∀ i, B i ⟶ Z i) (w : ∀ i, f i ≫ g i = 0)
    (h : ∀ i, IsColimit (CokernelCofork.ofπ (g i) (w i))) :
    IsColimit (CokernelCofork.ofπ (Sigma.map g) (show Sigma.map f ≫ Sigma.map g = 0 by
      ext i
      simp [reassoc_of% (w i)])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun k hk ↦ Sigma.desc fun i ↦ (h i).desc (CokernelCofork.ofπ (Sigma.ι B i ≫ k) (by
      rw [← Sigma.ι_map_assoc, hk, comp_zero])))
    (fun k hk ↦ by
      ext i
      simp only [Sigma.ι_map_assoc, colimit.ι_desc, Cofan.mk_ι_app]
      exact (h i).fac _ WalkingParallelPair.one)
    (fun k hk m hm ↦ by
      ext i
      simp only [colimit.ι_desc, Cofan.mk_ι_app]
      refine Cofork.IsColimit.hom_ext (h i) ?_
      refine Eq.trans ?_
        ((h i).fac (CokernelCofork.ofπ (Sigma.ι B i ≫ k) _) WalkingParallelPair.one).symm
      simp [← hm])

end CategoryTheory.Limits
