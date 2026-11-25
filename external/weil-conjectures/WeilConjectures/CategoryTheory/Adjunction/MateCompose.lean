/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!

# Mates of composite exchange transformations

Consider adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂`, `L₃ ⊣ R₃` with `L₁ : A ⥤ B`, `L₂ : B ⥤ C` and
`L₃ : A ⥤ C`, a composition isomorphism `e : L₃ ≅ L₁ ⋙ L₂`, and the same data `L₁', L₂', L₃', e'`
on a second row `A' ⥤ B' ⥤ C'`. Let `G : A ⥤ A'`, `H : B ⥤ B'` and `K : C ⥤ C'` be functors and

```
ν₁ : G ⋙ L₁' ⟶ L₁ ⋙ H,     ν₂ : H ⋙ L₂' ⟶ L₂ ⋙ K,     ν₃ : G ⋙ L₃' ⟶ L₃ ⋙ K
```

exchange transformations such that `ν₃` is the composite of `ν₁` and `ν₂` under `e` and `e'`.
Then the mates `β_i : R_i ⋙ (−) ⟶ (−) ⋙ R_i'` satisfy the composition law

```
β₃ = R₁' β₂ ∘ β₁ R₂
```

under the conjugate isomorphisms `R₃ ≅ R₂ ⋙ R₁` and `R₃' ≅ R₂' ⋙ R₁'` of `e` and `e'`
(`CategoryTheory.mateEquiv_app_comp_conjugateIsoEquiv_hom_app`).

For nearby cycles `Ψ`, with `L = Rf_!` and `R = Rf^!`, the `ν` are the compact-support exchanges
`Rf'_! Ψ ⟶ Ψ Rf_!` and their mates are the exceptional exchanges `Ψ Rf^! ⟶ Rf'^! Ψ`; this is the
composition law `β_{gf} = f_s^! β_g ∘ β_f(g^!)` of blueprint
`lemma-compatibilities-base-change-maps` (3).

-/

@[expose] public section

namespace CategoryTheory

variable {A B C A' B' C' : Type*} [Category A] [Category B] [Category C] [Category A']
  [Category B'] [Category C']
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L₃ : A ⥤ C} {R₃ : C ⥤ A}
  {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : B' ⥤ C'} {R₂' : C' ⥤ B'} {L₃' : A' ⥤ C'}
  {R₃' : C' ⥤ A'}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
  (adj₃' : L₃' ⊣ R₃') (e : L₃ ≅ L₁ ⋙ L₂) (e' : L₃' ≅ L₁' ⋙ L₂')
  {G : A ⥤ A'} {H : B ⥤ B'} {K : C ⥤ C'}
  (ν₁ : G ⋙ L₁' ⟶ L₁ ⋙ H) (ν₂ : H ⋙ L₂' ⟶ L₂ ⋙ K) (ν₃ : G ⋙ L₃' ⟶ L₃ ⋙ K)

/-- **Composition law for mates**: if the exchange `ν₃` of a composite is the composite of the
exchanges `ν₁` and `ν₂` under the composition isomorphisms `e : L₃ ≅ L₁ ⋙ L₂` and
`e' : L₃' ≅ L₁' ⋙ L₂'`, then its mate is the composite `R₁' β₂ ∘ β₁ R₂` of the mates, under the
conjugate isomorphisms `R₃ ≅ R₂ ⋙ R₁` and `R₃' ≅ R₂' ⋙ R₁'`. That is, the square
```
G R₃ c --------------------β₃-------------------> R₃' K c
   |                                                 |
   ≅                                                 ≅
   v                                                 v
G R₁ R₂ c --β₁ R₂--> R₁' H R₂ c --R₁' β₂--> R₁' R₂' K c
```
commutes. This is the pasting law for mates (`mateEquiv_vcomp`) read through the conjugates
(`conjugateEquiv`) of `e` and `e'`. -/
theorem mateEquiv_app_comp_conjugateIsoEquiv_hom_app
    (h : ∀ a : A, ν₃.app a ≫ K.map (e.hom.app a) =
      e'.hom.app (G.obj a) ≫ L₂'.map (ν₁.app a) ≫ ν₂.app (L₁.obj a)) (c : C) :
    (mateEquiv adj₃ adj₃' ν₃).app c ≫
        (conjugateIsoEquiv adj₃' (adj₁'.comp adj₂') e'.symm).hom.app (K.obj c) =
      G.map ((conjugateIsoEquiv adj₃ (adj₁.comp adj₂) e.symm).hom.app c) ≫
        (mateEquiv adj₁ adj₁' ν₁).app (R₂.obj c) ≫ R₁'.map ((mateEquiv adj₂ adj₂' ν₂).app c) := by
  apply ((adj₁'.comp adj₂').homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom]
  -- both transposes are `e'⁻¹ ≫ ν₃ ≫ K ε₃`
  trans e'.inv.app (G.obj (R₃.obj c)) ≫ ν₃.app (R₃.obj c) ≫ K.map (adj₃.counit.app c)
  · have h₁ := conjugateEquiv_counit adj₃' (adj₁'.comp adj₂') e'.inv (K.obj c)
    have h₂ : (L₁' ⋙ L₂').map ((mateEquiv adj₃ adj₃' ν₃).app c) ≫
        e'.inv.app (R₃'.obj (K.obj c)) =
        e'.inv.app _ ≫ L₃'.map ((mateEquiv adj₃ adj₃' ν₃).app c) :=
      e'.inv.naturality _
    have h₃ := mateEquiv_counit adj₃ adj₃' ν₃ c
    rw [Functor.map_comp, Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc, h₃]
    rfl
  · symm
    have hu := conjugateEquiv_counit adj₃ (adj₁.comp adj₂) e.inv c
    have he := e.hom.naturality ((conjugateEquiv adj₃ (adj₁.comp adj₂) e.inv).app c)
    have hν₃ := ν₃.naturality ((conjugateEquiv adj₃ (adj₁.comp adj₂) e.inv).app c)
    have he' := e'.inv.naturality (G.map ((conjugateEquiv adj₃ (adj₁.comp adj₂) e.inv).app c))
    have hh := h (R₁.obj (R₂.obj c))
    have hν₂ := ν₂.naturality (adj₁.counit.app (R₂.obj c))
    have hβ₂ := mateEquiv_counit adj₂ adj₂' ν₂ c
    have hβ₁ := mateEquiv_counit adj₁ adj₁' ν₁ (R₂.obj c)
    have hε₁ := adj₁'.counit.naturality ((mateEquiv adj₂ adj₂' ν₂).app c)
    simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj,
      Adjunction.comp_counit_app] at hu he hν₃ he' hh hν₂ hε₁ ⊢
    simp only [Functor.map_comp, Category.assoc]
    rw [← L₂'.map_comp_assoc (L₁'.map (R₁'.map _)), hε₁]
    simp only [Functor.map_comp, Category.assoc]
    rw [hβ₂, ← L₂'.map_comp_assoc (L₁'.map ((mateEquiv adj₁ adj₁' ν₁).app (R₂.obj c))), hβ₁]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hν₂]
    have hh' : L₂'.map (ν₁.app (R₁.obj (R₂.obj c))) ≫ ν₂.app (L₁.obj (R₁.obj (R₂.obj c))) =
        e'.inv.app _ ≫ ν₃.app (R₁.obj (R₂.obj c)) ≫ K.map (e.hom.app _) := by
      rw [hh, Iso.inv_hom_id_app_assoc]
    have he₂ : L₃.map (((conjugateEquiv adj₃ (adj₁.comp adj₂)) e.inv).app c) ≫
        e.hom.app (R₁.obj (R₂.obj c)) = e.hom.app (R₃.obj c) ≫
          L₂.map (L₁.map (((conjugateEquiv adj₃ (adj₁.comp adj₂)) e.inv).app c)) :=
      e.hom.naturality _
    have hK : K.map (L₃.map (((conjugateEquiv adj₃ (adj₁.comp adj₂)) e.inv).app c)) ≫
        K.map (e.hom.app (R₁.obj (R₂.obj c))) ≫ K.map (L₂.map (adj₁.counit.app (R₂.obj c))) ≫
          K.map (adj₂.counit.app c) = K.map (adj₃.counit.app c) := by
      simp only [← K.map_comp]
      congr 1
      rw [reassoc_of% he₂, hu, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% hh', reassoc_of% he', reassoc_of% hν₃, hK]

end CategoryTheory
