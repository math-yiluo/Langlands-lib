/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-!
# The tensor map of an adjunction whose counit is a trace

Let `adj : L ⊣ R` be an adjunction with a projection map `π M N : L M ⊗ N ⟶ L (M ⊗ F N)` which
is invertible, natural in `M` and associative with respect to a comparison
`δ : F (N ⊗ N') ≅ F N ⊗ F N'`. Suppose that the right adjoint is a twisted pullback,
`γ N : R N ≅ T ⊗ F N`, and that the counit is the *trace counit*

`ε_N : L (R N) ≅ L (T ⊗ F N) ≅ L T ⊗ N ⟶ 𝟙 ⊗ N ≅ N`

of a morphism `t : L T ⟶ 𝟙_` (for the projective line, `T = Λ(1)[2]` and `t` the trace). Then
the tensor map `τ M N : R M ⊗ F N ⟶ R (M ⊗ N)`
(`CategoryTheory.Adjunction.projectionTensorMap`) is the canonical reassociation
`(T ⊗ F M) ⊗ F N ≅ T ⊗ (F M ⊗ F N) ≅ T ⊗ F (M ⊗ N)`
(`CategoryTheory.Adjunction.projectionTensorMap_eq_of_counit_eq`); in particular it is an
isomorphism (`CategoryTheory.Adjunction.isIso_projectionTensorMap_of_counit_eq`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]
  (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
  (δ : ∀ N N' : D, F.obj (N ⊗ N') ⟶ F.obj N ⊗ F.obj N') [∀ N N', IsIso (δ N N')]
  (hassoc : ∀ (M : C) (N N' : D), π M N ▷ N' ≫ π (M ⊗ F.obj N) N' ≫
    L.map (α_ M (F.obj N) (F.obj N')).hom = (α_ _ N N').hom ≫ π M (N ⊗ N') ≫ L.map (M ◁ δ N N'))
  (T : C) (t : L.obj T ⟶ 𝟙_ D) (γ : ∀ N : D, R.obj N ≅ T ⊗ F.obj N)
  (hε : ∀ N : D, adj.counit.app N =
    L.map (γ N).hom ≫ inv (π T N) ≫ t ▷ N ≫ (λ_ N).hom)
include hπ hassoc hε

/-- **The tensor map of a trace counit is the reassociation.** If the counit of `L ⊣ R` is the
trace counit `L (R N) ≅ L (T ⊗ F N) ≅ L T ⊗ N ⟶ N` of `t : L T ⟶ 𝟙_` through
`γ N : R N ≅ T ⊗ F N`, then the tensor map `τ M N : R M ⊗ F N ⟶ R (M ⊗ N)` is
`(T ⊗ F M) ⊗ F N ≅ T ⊗ (F M ⊗ F N) ≅ T ⊗ F (M ⊗ N)`, read through `γ`:

```
  R M ⊗ F N  -----------------τ----------------->  R (M ⊗ N)
     |                                                ↑
  γ_M ▷ F N                                      γ_{M ⊗ N}⁻¹
     ↓                                                |
  (T ⊗ F M) ⊗ F N --α--> T ⊗ (F M ⊗ F N) --T ◁ δ⁻¹--> T ⊗ F (M ⊗ N)
```
-/
theorem projectionTensorMap_eq_of_counit_eq (M N : D) :
    adj.projectionTensorMap π M N =
      (γ M).hom ▷ F.obj N ≫ (α_ T (F.obj M) (F.obj N)).hom ≫ T ◁ inv (δ M N) ≫
        (γ (M ⊗ N)).inv := by
  apply ext_of_comp_counit (adj := adj)
  rw [map_projectionTensorMap_comp_counit, hε, hε]
  -- the projection map is natural in its first variable
  have h₁ : inv (π (R.obj M) N) ≫ L.map (γ M).hom ▷ N =
      L.map ((γ M).hom ▷ F.obj N) ≫ inv (π (T ⊗ F.obj M) N) := by
    rw [IsIso.eq_comp_inv, Category.assoc, hπ, IsIso.inv_hom_id_assoc]
  -- the projection map is associative
  have h₂ : inv (π (T ⊗ F.obj M) N) ≫ inv (π T M) ▷ N =
      L.map (α_ T (F.obj M) (F.obj N)).hom ≫ L.map (T ◁ inv (δ M N)) ≫ inv (π T (M ⊗ N)) ≫
        (α_ (L.obj T) M N).inv := by
    have h := hassoc T M N
    have h' : L.map ((α_ T (F.obj M) (F.obj N)).hom ≫ T ◁ inv (δ M N)) =
        inv (π (T ⊗ F.obj M) N) ≫ inv (π T M ▷ N) ≫ (α_ (L.obj T) M N).hom ≫ π T (M ⊗ N) := by
      rw [Functor.map_comp, ← cancel_epi (π T M ▷ N ≫ π (T ⊗ F.obj M) N), Category.assoc,
        reassoc_of% h]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc, ← Functor.map_comp, ← whiskerLeft_comp,
        IsIso.hom_inv_id, whiskerLeft_id, Functor.map_id, Category.comp_id]
    rw [← Functor.map_comp_assoc, h']
    simp [inv_whiskerRight]
  simp only [comp_whiskerRight, Category.assoc, Functor.map_comp]
  rw [reassoc_of% h₁, reassoc_of% h₂, ← L.map_comp_assoc (γ (M ⊗ N)).inv, Iso.inv_hom_id,
    L.map_id, Category.id_comp]
  congr 4
  -- the remaining identity is monoidal coherence
  rw [← associator_inv_naturality_left_assoc]
  simp

/-- **The tensor map of a trace counit is an isomorphism.** -/
theorem isIso_projectionTensorMap_of_counit_eq (M N : D) :
    IsIso (adj.projectionTensorMap π M N) := by
  rw [projectionTensorMap_eq_of_counit_eq adj π hπ δ hassoc T t γ hε M N]
  infer_instance

end CategoryTheory.Adjunction
