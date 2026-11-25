/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection

/-!
# The open complement of the zero section of the affine line

The multiplicative group `𝔾_{m,S}` is carried in this project as a scheme `G` with an open
immersion `j : G ⟶ 𝔸¹_S` whose range is the complement of the zero section. This file shows
that this notion is stable under base change: for `g : S' ⟶ S` and such data `(G, j)` over `S`
and `(G', j')` over `S'`, the morphism `𝔸¹_{S'} ⟶ 𝔸¹_S` restricts to `G' ⟶ G`, and the squares

```
  G' ----> G           G' -----> G
  |        |           |         |
  j'       j           π'        π
  v        v           v         v
𝔸¹_{S'} -> 𝔸¹_S        S' --g--> S
```

are cartesian (`AlgebraicGeometry.AffineSpace.isPullback_complementMap`,
`AlgebraicGeometry.AffineSpace.isPullback_complementMap_over`). The basic open of the coordinate
is such a complement (`AlgebraicGeometry.AffineSpace.range_basicOpen_ι_coord`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineSpace

variable {S : Scheme.{u}}

/-- The complement of the zero section of the affine line is the basic open of the
coordinate. -/
lemma compl_range_zeroSection (S : Scheme.{u}) :
    (Set.range (zeroSection (ULift.{u} (Fin 1)) S).base)ᶜ =
      (𝔸(ULift.{u} (Fin 1); S).basicOpen (coord S (ULift.up 0)) : Set 𝔸(ULift.{u} (Fin 1); S)) := by
  ext y
  simp [range_zeroSection, Unique.forall_iff]
  rfl

/-- The basic open of the coordinate is the open complement of the zero section. -/
lemma range_basicOpen_ι_coord (S : Scheme.{u}) :
    Set.range (𝔸(ULift.{u} (Fin 1); S).basicOpen (coord S (ULift.up 0))).ι.base =
      (Set.range (zeroSection (ULift.{u} (Fin 1)) S).base)ᶜ := by
  rw [Scheme.Opens.range_ι, compl_range_zeroSection]

/-- The zero section is stable under base change: its preimage along `𝔸¹_{S'} ⟶ 𝔸¹_S` is the
zero section. -/
lemma preimage_range_zeroSection {S' : Scheme.{u}} (g : S' ⟶ S) :
    (map (ULift.{u} (Fin 1)) g).base ⁻¹' Set.range (zeroSection (ULift.{u} (Fin 1)) S).base =
      Set.range (zeroSection (ULift.{u} (Fin 1)) S').base := by
  rw [range_zeroSection, range_zeroSection]
  ext y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  refine forall_congr' fun i ↦ not_congr ?_
  change y ∈ map (ULift.{u} (Fin 1)) g ⁻¹ᵁ 𝔸(ULift.{u} (Fin 1); S).basicOpen (coord S i) ↔ _
  rw [Scheme.preimage_basicOpen_top, map_appTop_coord]

variable {S' : Scheme.{u}} (g : S' ⟶ S) {G G' : Scheme.{u}}
  (j : G ⟶ 𝔸(ULift.{u} (Fin 1); S)) [IsOpenImmersion j]
  (j' : G' ⟶ 𝔸(ULift.{u} (Fin 1); S')) [IsOpenImmersion j']

/-- The restriction `G' ⟶ G` of `𝔸¹_{S'} ⟶ 𝔸¹_S` to the complements of the zero sections. -/
noncomputable def complementMap
    (hj : Set.range j.base = (Set.range (zeroSection (ULift.{u} (Fin 1)) S).base)ᶜ)
    (hj' : Set.range j'.base = (Set.range (zeroSection (ULift.{u} (Fin 1)) S').base)ᶜ) :
    G' ⟶ G :=
  IsOpenImmersion.lift j (j' ≫ map (ULift.{u} (Fin 1)) g) (by
    rintro _ ⟨x, rfl⟩
    rw [hj]
    intro hx
    have : j'.base x ∈ Set.range (zeroSection (ULift.{u} (Fin 1)) S').base := by
      rw [← preimage_range_zeroSection g]
      simpa using hx
    have h₂ : j'.base x ∈ (Set.range (zeroSection (ULift.{u} (Fin 1)) S').base)ᶜ :=
      hj' ▸ ⟨x, rfl⟩
    exact h₂ this)

variable (hj : Set.range j.base = (Set.range (zeroSection (ULift.{u} (Fin 1)) S).base)ᶜ)
  (hj' : Set.range j'.base = (Set.range (zeroSection (ULift.{u} (Fin 1)) S').base)ᶜ)

omit [IsOpenImmersion j'] in
@[reassoc (attr := simp)]
lemma complementMap_comp :
    complementMap g j j' hj hj' ≫ j = j' ≫ map (ULift.{u} (Fin 1)) g :=
  IsOpenImmersion.lift_fac _ _ _

/-- The complement of the zero section is stable under base change. -/
lemma isPullback_complementMap :
    IsPullback (complementMap g j j' hj hj') j' j (map (ULift.{u} (Fin 1)) g) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (complementMap_comp g j j' hj hj').symm ?_
  ext x
  change (map (ULift.{u} (Fin 1)) g).base x ∈ Set.range j.base ↔ x ∈ Set.range j'.base
  rw [hj, hj', ← preimage_range_zeroSection g]
  rfl

/-- The projection `G ⟶ S` of the complement of the zero section is stable under base change. -/
lemma isPullback_complementMap_over :
    IsPullback (complementMap g j j' hj hj') (j' ≫ 𝔸(ULift.{u} (Fin 1); S') ↘ S')
      (j ≫ 𝔸(ULift.{u} (Fin 1); S) ↘ S) g :=
  (isPullback_complementMap g j j' hj hj').paste_vert (isPullback_map g)

omit [IsOpenImmersion j'] [IsOpenImmersion j] in
include hj in
/-- The base change of the complement of the zero section is the complement of the zero
section. -/
lemma range_pullback_snd_map :
    Set.range (pullback.snd j (map (ULift.{u} (Fin 1)) g)).base =
      (Set.range (zeroSection (ULift.{u} (Fin 1)) S').base)ᶜ := by
  rw [Scheme.Pullback.range_snd, hj, Set.preimage_compl, preimage_range_zeroSection]

end AlgebraicGeometry.AffineSpace
