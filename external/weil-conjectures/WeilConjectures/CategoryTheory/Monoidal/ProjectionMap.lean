/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Projection maps tensored with a fixed object

Let `π_{K, L} : R K ⊗ L ⟶ R (K ⊗ P L)` be a projection map satisfying the associativity law for
a comparison `δ : P (L ⊗ L') ⟶ P L ⊗ P L'`, and let `a : P N_Y ⟶ N_X`. We compare `π_{K, L} ▷ N_Y`
with `π_{K, L ⊗ N_Y}` through the induced comparison `c_M = π_{M, N_Y} ≫ R (M ◁ a)`
(`CategoryTheory.Adjunction.projectionMap_whiskerRight_comp`), and deduce that one is an
isomorphism if and only if the other is
(`CategoryTheory.Adjunction.isIso_projectionMap_whiskerRight_iff`). This is the formal input for
the compatibility of the projection formula for compactly supported direct images with finite
reduction of coefficients (blueprint `sk-prop-sf-pf-reduction`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category MonoidalCategory

section TensorRight

variable {CX CY : Type*} [Category* CX] [Category* CY] [MonoidalCategory CX]
  [MonoidalCategory CY] {R : CX ⥤ CY} {P : CY ⥤ CX}
  {δ : ∀ L L', P.obj (L ⊗ L') ⟶ P.obj L ⊗ P.obj L'}
  (π : ∀ K L, R.obj K ⊗ L ⟶ R.obj (K ⊗ P.obj L))
  (hπ : ∀ K L L', π K L ▷ L' ≫ π (K ⊗ P.obj L) L' ≫ R.map (α_ K (P.obj L) (P.obj L')).hom =
    (α_ (R.obj K) L L').hom ≫ π K (L ⊗ L') ≫ R.map (K ◁ δ L L'))
  {NY : CY} {NX : CX} (a : P.obj NY ⟶ NX)

include hπ in
/-- **Tensoring a projection map with a fixed object.** Let `π_{K, L} : R K ⊗ L ⟶ R (K ⊗ P L)`
be a projection map satisfying the associativity law for a comparison
`δ : P (L ⊗ L') ⟶ P L ⊗ P L'`, and let `a : P N_Y ⟶ N_X`. Write
`c_M = π_{M, N_Y} ≫ R (M ◁ a) : R M ⊗ N_Y ⟶ R (M ⊗ N_X)` for the induced comparison of `R`
with `- ⊗ N`. Then the square
```
(R K ⊗ L) ⊗ N_Y --π_{K, L} ▷ N_Y--> R (K ⊗ P L) ⊗ N_Y ------c------> R ((K ⊗ P L) ⊗ N_X)
      | α                                                                  ^ R α⁻¹
      v                                                                    |
R K ⊗ (L ⊗ N_Y) --π--> R (K ⊗ P (L ⊗ N_Y)) --R (K ◁ (δ ≫ P L ◁ a))--> R (K ⊗ (P L ⊗ N_X))
```
commutes. -/
lemma projectionMap_whiskerRight_comp (K : CX) (L : CY) :
    π K L ▷ NY ≫ π (K ⊗ P.obj L) NY ≫ R.map ((K ⊗ P.obj L) ◁ a) =
      (α_ (R.obj K) L NY).hom ≫ π K (L ⊗ NY) ≫ R.map (K ◁ (δ L NY ≫ P.obj L ◁ a)) ≫
        R.map (α_ K (P.obj L) NX).inv := by
  have h : π K L ▷ NY ≫ π (K ⊗ P.obj L) NY = (α_ (R.obj K) L NY).hom ≫ π K (L ⊗ NY) ≫
      R.map (K ◁ δ L NY) ≫ R.map (α_ K (P.obj L) (P.obj NY)).inv := by
    rw [← reassoc_of% (hπ K L NY), ← R.map_comp, Iso.hom_inv_id, R.map_id, comp_id]
  rw [reassoc_of% h]
  simp only [← R.map_comp, MonoidalCategory.whiskerLeft_comp, assoc,
    associator_inv_naturality_right]

/-- The comparison `c_K = π_{K, N_Y} ≫ R (K ◁ a)` of
`CategoryTheory.Adjunction.projectionMap_whiskerRight_comp` is natural in `K` if `π` is. -/
lemma projectionMap_comp_map_whiskerLeft_naturality
    (hnat : ∀ {K K'} (φ : K ⟶ K') L, R.map φ ▷ L ≫ π K' L = π K L ≫ R.map (φ ▷ P.obj L))
    {K K' : CX} (φ : K ⟶ K') :
    R.map φ ▷ NY ≫ π K' NY ≫ R.map (K' ◁ a) = (π K NY ≫ R.map (K ◁ a)) ≫ R.map (φ ▷ NX) := by
  rw [reassoc_of% (hnat φ NY), assoc, ← R.map_comp, ← R.map_comp, whisker_exchange]

include hπ in
/-- With the notation of `CategoryTheory.Adjunction.projectionMap_whiskerRight_comp`: if `a`,
`δ` and the comparison `c_{K ⊗ P L}` are isomorphisms, then `π_{K, L} ▷ N_Y` is an isomorphism if
and only if `π_{K, L ⊗ N_Y}` is. -/
lemma isIso_projectionMap_whiskerRight_iff [IsIso a] (K : CX) (L : CY)
    [IsIso (δ L NY)] (hc : IsIso (π (K ⊗ P.obj L) NY ≫ R.map ((K ⊗ P.obj L) ◁ a))) :
    IsIso (π K L ▷ NY) ↔ IsIso (π K (L ⊗ NY)) := by
  rw [← isIso_comp_right_iff _ (π (K ⊗ P.obj L) NY ≫ R.map ((K ⊗ P.obj L) ◁ a)),
    projectionMap_whiskerRight_comp π hπ, isIso_comp_left_iff, ← assoc, isIso_comp_right_iff,
    isIso_comp_right_iff]

end TensorRight

end CategoryTheory.Adjunction
