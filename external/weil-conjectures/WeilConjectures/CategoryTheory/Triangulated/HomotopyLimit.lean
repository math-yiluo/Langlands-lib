/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Homotopy limits of towers in a pretriangulated category

Let `F : ℕᵒᵖ ⥤ C` be a tower `⋯ ⟶ F₂ ⟶ F₁ ⟶ F₀` in a pretriangulated category. A categorical
limit of `F` rarely exists in a triangulated category, and when it does it is not the derived
limit. The *homotopy limit* `R lim F` is instead characterised, up to non-unique isomorphism,
by the Milnor (or Roos) triangle

```
  R lim F ⟶ ∏ₙ Fₙ ──1 - t──▶ ∏ₙ Fₙ ⟶ (R lim F)[1]
```

where `t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ` has components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`. In the derived category of an
abelian category with exact countable products, such as sheaves on a replete topos, this is
the derived functor of `lim` applied to the tower.

## Main definitions

- `CategoryTheory.Pretriangulated.towerShift`: the map `t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ`.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit`: a cone over a tower is a homotopy limit
  cone if its legs fit into a distinguished Milnor triangle.

## Main statements

- `CategoryTheory.Pretriangulated.IsHomotopyLimit.of_iso`: being a homotopy limit cone is
  invariant under isomorphisms of towers and of cone points.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.map`: a triangulated functor preserving the
  product `∏ₙ Fₙ` sends homotopy limit cones to homotopy limit cones.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.exists_iso`: homotopy limits are unique up to
  isomorphism compatible with the legs.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.of_isIso_π`: a cone whose legs are all
  isomorphisms is a homotopy limit cone.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.of_isIso_π_succ`: the same, for a cone whose
  legs are isomorphisms in all positive degrees.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The transition endomorphism `t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ` of a product of the terms of a tower
`F : ℕᵒᵖ ⥤ C`, with components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`. -/
noncomputable def towerShift {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)}
    (hP : IsLimit P) : P.pt ⟶ P.pt :=
  Fan.IsLimit.lift hP fun n ↦ P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op

/-- A cone `c` over a tower `F : ℕᵒᵖ ⥤ C` is a *homotopy limit* cone if, for a product
`∏ₙ Fₙ`, the Milnor triangle

```
  c.pt ──(c.π n)ₙ──▶ ∏ₙ Fₙ ──1 - t──▶ ∏ₙ Fₙ ──δ──▶ c.pt⟦1⟧
```

is distinguished for some `δ`, where `t` is `towerShift`. The point of a homotopy limit cone is
then the derived limit `R lim F`, determined up to non-unique isomorphism. -/
def IsHomotopyLimit {F : ℕᵒᵖ ⥤ C} (c : Cone F) : Prop :=
  ∃ (P : Fan fun n : ℕ ↦ F.obj (op n)) (hP : IsLimit P) (δ : P.pt ⟶ c.pt⟦(1 : ℤ)⟧),
    Triangle.mk (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) (𝟙 P.pt - towerShift hP) δ ∈
      distTriang C

namespace IsHomotopyLimit

/-- Being a homotopy limit cone is invariant under isomorphisms: if `c` is a homotopy limit
cone over `F`, `e : F ≅ G` and `eπ : c.pt ≅ c'.pt` are compatible with the legs, then `c'` is a
homotopy limit cone over `G`. -/
lemma of_iso {F G : ℕᵒᵖ ⥤ C} (e : F ≅ G) {c : Cone F} (hc : IsHomotopyLimit c) (c' : Cone G)
    (eπ : c.pt ≅ c'.pt)
    (h : ∀ n : ℕ, c.π.app (op n) ≫ e.hom.app (op n) = eπ.hom ≫ c'.π.app (op n)) :
    IsHomotopyLimit c' := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  let P' : Fan fun n : ℕ ↦ G.obj (op n) := Fan.mk P.pt fun n ↦ P.proj n ≫ e.hom.app (op n)
  have hP' : IsLimit P' := Fan.IsLimit.mk _
    (fun s ↦ Fan.IsLimit.lift hP fun n ↦ s.proj n ≫ e.inv.app (op n))
    (fun s n ↦ by simp [P'])
    (fun s m hm ↦ Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp [← hm n, P'])
  have ht : towerShift hP' = towerShift hP := Fan.IsLimit.hom_ext hP' _ _ fun n ↦ by
    rw [towerShift, Fan.IsLimit.fac]
    simp only [P', fan_mk_proj, towerShift, Category.assoc, Fan.IsLimit.fac_assoc,
      NatTrans.naturality]
  refine ⟨P', hP', δ ≫ (shiftFunctor C (1 : ℤ)).map eπ.hom,
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ eπ.symm (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_)⟩
  · refine Fan.IsLimit.hom_ext hP' _ _ fun n ↦ ?_
    simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, Fan.IsLimit.fac,
      Iso.symm_hom, Category.assoc]
    simp only [P', fan_mk_proj, Fan.IsLimit.fac_assoc, h, Iso.inv_hom_id_assoc]
  · simp only [Triangle.mk_mor₂, Iso.refl_hom, Category.comp_id, Category.id_comp, ht]
    rfl
  · simp [← Functor.map_comp]

/-- Homotopy limits are unique up to (non-unique) isomorphism: if `c` and `c'` are homotopy
limit cones over the same tower, there is an isomorphism `c.pt ≅ c'.pt` compatible with the
legs. It is obtained by completing the identity of `∏ₙ Fₙ` to a morphism of Milnor triangles. -/
lemma exists_iso {F : ℕᵒᵖ ⥤ C} {c c' : Cone F} (hc : IsHomotopyLimit c)
    (hc' : IsHomotopyLimit c') :
    ∃ e : c.pt ≅ c'.pt, ∀ n : ℕ, e.hom ≫ c'.π.app (op n) = c.π.app (op n) := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  obtain ⟨P', hP', δ', hT'⟩ := hc'
  let eP : P.pt ≅ P'.pt := hP.conePointUniqueUpToIso hP'
  have heP (n : ℕ) : eP.hom ≫ P'.proj n = P.proj n :=
    hP.conePointUniqueUpToIso_hom_comp hP' ⟨n⟩
  have ht : towerShift hP ≫ eP.hom = eP.hom ≫ towerShift hP' :=
    Fan.IsLimit.hom_ext hP' _ _ fun n ↦ by
      simp only [Category.assoc, heP, towerShift, Fan.IsLimit.fac]
      rw [← Category.assoc, heP]
  have hcomm : (𝟙 P.pt - towerShift hP) ≫ eP.hom = eP.hom ≫ (𝟙 P'.pt - towerShift hP') := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub, ht, Category.id_comp, Category.comp_id]
  obtain ⟨a, ha₁, ha₃⟩ :=
    complete_distinguished_triangle_morphism₁ _ _ hT hT' eP.hom eP.hom hcomm
  have : IsIso a := isIso₁_of_isIso₂₃ (Triangle.homMk _ _ a eP.hom eP.hom ha₁ hcomm ha₃) hT hT'
    eP.isIso_hom eP.isIso_hom
  refine ⟨asIso a, fun n ↦ ?_⟩
  have := ha₁ =≫ P'.proj n
  simp only [Triangle.mk_mor₁, Category.assoc, heP, Fan.IsLimit.fac] at this
  simpa using this.symm

set_option backward.defeqAttrib.useBackward true in
/-- A cone over a tower whose legs are all isomorphisms (so that the tower is constant up to
isomorphism) is a homotopy limit cone: its Milnor triangle is split, `1 - t` having the section
`y ↦ (-∑_{k < n} y_k)_n` (transported along the transition isomorphisms). -/
lemma of_isIso_π {F : ℕᵒᵖ ⥤ C} (c : Cone F) [∀ n, IsIso (c.π.app n)]
    [HasProduct fun n : ℕ ↦ F.obj (op n)] : IsHomotopyLimit c := by
  let P : Fan fun n : ℕ ↦ F.obj (op n) := Fan.mk _ (Pi.π _)
  let hP : IsLimit P := productIsProduct _
  let ρ (n : ℕ) : F.obj (op n) ⟶ c.pt := inv (c.π.app (op n))
  let g (n : ℕ) : P.pt ⟶ c.pt := P.proj n ≫ ρ n
  have hτ (k : ℕ) : F.map (homOfLE k.le_succ).op ≫ ρ k = ρ (k + 1) := by
    refine IsIso.eq_inv_of_hom_inv_id ?_
    rw [← Category.assoc, c.w, IsIso.hom_inv_id]
  have hg (k : ℕ) : (𝟙 P.pt - towerShift hP) ≫ g k = g k - g (k + 1) := by
    simp only [g, Preadditive.sub_comp, Category.id_comp, towerShift, Fan.IsLimit.fac_assoc,
      Category.assoc, hτ]
  have hgπ (n : ℕ) : g n ≫ c.π.app (op n) = P.proj n := by simp [g, ρ]
  let ℓ : c.pt ⟶ P.pt := Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)
  let σ : P.pt ⟶ P.pt :=
    Fan.IsLimit.lift hP fun n ↦ -(∑ k ∈ Finset.range n, g k) ≫ c.π.app (op n)
  have hℓg : ℓ ≫ g 0 = 𝟙 _ := by simp [ℓ, g, ρ]
  have hℓt : ℓ ≫ (𝟙 P.pt - towerShift hP) = 0 := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
    simp [ℓ, Preadditive.sub_comp, towerShift, c.w]
  have hσg : σ ≫ g 0 = 0 := by simp [σ, g]
  have hσt : σ ≫ (𝟙 P.pt - towerShift hP) = 𝟙 _ := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
    simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp, Category.assoc,
      towerShift, Fan.IsLimit.fac, Category.id_comp, σ, Fan.IsLimit.fac_assoc, c.w,
      Finset.sum_range_succ, Preadditive.neg_comp, Preadditive.add_comp, hgπ, neg_add_rev]
    abel
  have hsplit : g 0 ≫ ℓ + (𝟙 P.pt - towerShift hP) ≫ σ = 𝟙 _ :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      have h₁ : (g 0 ≫ ℓ) ≫ P.proj n = g 0 ≫ c.π.app (op n) := by
        simp [ℓ]
      have h₂ : ((𝟙 P.pt - towerShift hP) ≫ σ) ≫ P.proj n =
          -(g 0 - g n) ≫ c.π.app (op n) := by
        rw [Category.assoc, Fan.IsLimit.fac, Preadditive.comp_neg, ← Category.assoc,
          Preadditive.comp_sum]
        simp only [hg, Finset.sum_range_sub']
      rw [Preadditive.add_comp, h₁, h₂, Preadditive.sub_comp, hgπ,
        Category.id_comp]
      abel
  let e : P.pt ≅ c.pt ⊞ P.pt :=
    { hom := biprod.lift (g 0) (𝟙 P.pt - towerShift hP)
      inv := biprod.desc ℓ σ
      hom_inv_id := by rw [biprod.lift_desc, hsplit]
      inv_hom_id := by
        apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
          simp [hℓg, hℓt, hσg, hσt] }
  refine ⟨P, hP, 0, isomorphic_distinguished _ (binaryBiproductTriangle_distinguished c.pt P.pt)
    _ (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_)⟩
  · apply biprod.hom_ext <;> simp [e, hℓg, hℓt, ℓ]
  · simp [e]
  · simp

set_option backward.defeqAttrib.useBackward true in
/-- A cone over a tower whose legs are isomorphisms in all positive degrees is a homotopy limit
cone: the term `F₀` does not matter. As in `IsHomotopyLimit.of_isIso_π`, the Milnor triangle
is split, `1 - t` having the section `y ↦ (y₀, (-∑_{1 ≤ k < n} y_k)_{n ≥ 1})` (transported along
the transition isomorphisms in positive degrees). -/
lemma of_isIso_π_succ {F : ℕᵒᵖ ⥤ C} (c : Cone F) [∀ n : ℕ, IsIso (c.π.app (op (n + 1)))]
    [HasProduct fun n : ℕ ↦ F.obj (op n)] : IsHomotopyLimit c := by
  let P : Fan fun n : ℕ ↦ F.obj (op n) := Fan.mk _ (Pi.π _)
  let hP : IsLimit P := productIsProduct _
  let h (k : ℕ) : P.pt ⟶ c.pt := P.proj (k + 1) ≫ inv (c.π.app (op (k + 1)))
  have hw (k : ℕ) : c.π.app (op (k + 1)) ≫ F.map (homOfLE k.le_succ).op = c.π.app (op k) :=
    c.w _
  have hτ (k : ℕ) : F.map (homOfLE (k + 1).le_succ).op ≫ inv (c.π.app (op (k + 1))) =
      inv (c.π.app (op (k + 1 + 1))) := by
    refine IsIso.eq_inv_of_hom_inv_id ?_
    rw [← Category.assoc, hw, IsIso.hom_inv_id]
  have hinv (k : ℕ) : inv (c.π.app (op (k + 1))) ≫ c.π.app (op k) =
      F.map (homOfLE k.le_succ).op := by
    rw [IsIso.inv_comp_eq, hw]
  have hh (k : ℕ) : (𝟙 P.pt - towerShift hP) ≫ h k = h k - h (k + 1) := by
    simp only [h, Preadditive.sub_comp, Category.id_comp, towerShift, Fan.IsLimit.fac_assoc,
      Category.assoc, hτ]
  have hhπ (n : ℕ) : h n ≫ c.π.app (op (n + 1)) = P.proj (n + 1) := by simp [h]
  let ℓ : c.pt ⟶ P.pt := Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)
  let σc : ∀ n : ℕ, P.pt ⟶ F.obj (op n) := fun n ↦ match n with
    | 0 => P.proj 0
    | m + 1 => -(∑ k ∈ Finset.range m, h k) ≫ c.π.app (op (m + 1))
  let σ : P.pt ⟶ P.pt := Fan.IsLimit.lift hP σc
  have hℓg : ℓ ≫ h 0 = 𝟙 _ := by simp [ℓ, h]
  have hℓt : ℓ ≫ (𝟙 P.pt - towerShift hP) = 0 := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
    simp [ℓ, Preadditive.sub_comp, towerShift, c.w]
  have hσg : σ ≫ h 0 = 0 := by simp [σ, h, σc]
  have hσt : σ ≫ (𝟙 P.pt - towerShift hP) = 𝟙 _ := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
    rcases n with _ | m
    · simp [σ, σc, Preadditive.sub_comp, towerShift]
    · simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp, Category.assoc,
        towerShift, Fan.IsLimit.fac, Category.id_comp, σ, σc, Fan.IsLimit.fac_assoc, hw,
        Finset.sum_range_succ, Preadditive.neg_comp, Preadditive.add_comp, hhπ, neg_add_rev]
      abel
  have hsplit : h 0 ≫ ℓ + (𝟙 P.pt - towerShift hP) ≫ σ = 𝟙 _ :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      rcases n with _ | m
      · simp only [Preadditive.add_comp, Category.assoc, Fan.IsLimit.fac, ℓ, σ, σc,
          Preadditive.sub_comp, Category.id_comp, towerShift, h, hinv]
        simp
      · have h₂ : ((𝟙 P.pt - towerShift hP) ≫ σ) ≫ P.proj (m + 1) =
            -(h 0 - h m) ≫ c.π.app (op (m + 1)) := by
          rw [Category.assoc, Fan.IsLimit.fac, Preadditive.comp_neg, ← Category.assoc,
            Preadditive.comp_sum]
          simp only [hh, Finset.sum_range_sub']
        rw [Preadditive.add_comp, h₂, Category.assoc, Fan.IsLimit.fac]
        simp only [Preadditive.sub_comp, hhπ, Category.id_comp]
        abel
  let e : P.pt ≅ c.pt ⊞ P.pt :=
    { hom := biprod.lift (h 0) (𝟙 P.pt - towerShift hP)
      inv := biprod.desc ℓ σ
      hom_inv_id := by rw [biprod.lift_desc, hsplit]
      inv_hom_id := by
        apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
          simp [hℓg, hℓt, hσg, hσt] }
  refine ⟨P, hP, 0, isomorphic_distinguished _ (binaryBiproductTriangle_distinguished c.pt P.pt)
    _ (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_)⟩
  · apply biprod.hom_ext <;> simp [e, hℓg, hℓt, ℓ]
  · simp [e]
  · simp

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A triangulated functor `Φ` that preserves the product `∏ₙ Fₙ` sends a homotopy limit
cone over `F` to a homotopy limit cone over `F ⋙ Φ`: it sends the Milnor triangle of `F` to that
of `F ⋙ Φ`. -/
lemma map {F : ℕᵒᵖ ⥤ C} {c : Cone F} (hc : IsHomotopyLimit c) (Φ : C ⥤ D) [Φ.CommShift ℤ]
    [Φ.IsTriangulated] [Φ.Additive]
    [PreservesLimit (Discrete.functor fun n : ℕ ↦ F.obj (op n)) Φ] :
    IsHomotopyLimit (Φ.mapCone c) := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  let hP' := isLimitFanMkObjOfIsLimit Φ (fun n : ℕ ↦ F.obj (op n)) P.proj hP
  have ht : towerShift (F := F ⋙ Φ) hP' = Φ.map (towerShift hP) :=
    Fan.IsLimit.hom_ext hP' _ _ fun n ↦ by
      rw [towerShift, Fan.IsLimit.fac]
      simp only [fan_mk_proj, Functor.comp_map, ← Functor.map_comp, towerShift,
        Fan.IsLimit.fac]
  refine ⟨_, hP', Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app c.pt,
    isomorphic_distinguished _ (Φ.map_distinguished _ hT) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)⟩
  · refine Fan.IsLimit.hom_ext hP' _ _ fun n ↦ ?_
    simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, Category.id_comp]
    rw [Fan.IsLimit.fac]
    change _ = Φ.map (Fan.IsLimit.lift hP _) ≫ Φ.map (P.proj n)
    rw [← Functor.map_comp, Fan.IsLimit.fac]
    rfl
  · simp only [Triangle.mk_mor₂, Iso.refl_hom, Category.comp_id, Category.id_comp]
    change _ = Φ.map (𝟙 P.pt - towerShift hP)
    rw [ht, Functor.map_sub, Functor.map_id]
    rfl
  · simp only [Iso.refl_hom, Functor.map_id, Category.comp_id, Category.id_comp]
    rfl

end IsHomotopyLimit

end CategoryTheory.Pretriangulated
