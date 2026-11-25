/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Data.Fintype.BigOperators

/-!
# Linear forms with a unit coefficient are coordinates

Let `g : T ⟶ S` and let `c : n → Γ(T, 𝒪)` be coefficients with `cᵢ` a unit. On the base change
`𝔸(n; S) ×_S T` of relative affine space, the linear form `ℓ = ∑ⱼ cⱼ xⱼ`
(`AlgebraicGeometry.AffineSpace.linearForm`) is a coordinate: the linear change of variables
keeping the `xⱼ`, `j ≠ i`, and replacing `xᵢ` by `ℓ` is an isomorphism
`𝔸(n; S) ×_S T ≅ 𝔸¹(𝔸(n ∖ {i}; T))` over `T` carrying `ℓ` to the coordinate of the affine line.

## Main definitions

- `AlgebraicGeometry.AffineSpace.linearForm`: the linear form `∑ⱼ cⱼ xⱼ`.
- `AlgebraicGeometry.AffineSpace.linearCoordHom`: the change of variables
  `𝔸(n; S) ×_S T ⟶ 𝔸¹(𝔸(n ∖ {i}; T))`.
- `AlgebraicGeometry.AffineSpace.linearCoordInv`: its inverse, when `cᵢ` is a unit.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineSpace

variable {n : Type u} [Fintype n] {S T : Scheme.{u}} (g : T ⟶ S) (c : n → Γ(T, ⊤))

/-- The linear form `x ↦ ∑ⱼ cⱼ xⱼ` on the base change `𝔸(n; S) ×_S T` of affine space along
`g : T ⟶ S`, for coefficients `c : n → Γ(T, 𝒪)`. -/
noncomputable def linearForm : Γ(pullback (𝔸(n; S) ↘ S) g, ⊤) :=
  ∑ j, (pullback.fst (𝔸(n; S) ↘ S) g).appTop (coord S j) *
    (pullback.snd (𝔸(n; S) ↘ S) g).appTop (c j)

variable (i : n)

/-- The linear change of coordinates `𝔸(n; S) ×_S T ⟶ 𝔸¹(𝔸(n ∖ {i}; T))`, keeping the
coordinates `xⱼ`, `j ≠ i`, and replacing `xᵢ` by the linear form `∑ⱼ cⱼ xⱼ`. -/
noncomputable def linearCoordHom :
    pullback (𝔸(n; S) ↘ S) g ⟶ 𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) :=
  homOfVector (homOfVector (pullback.snd (𝔸(n; S) ↘ S) g)
    fun j ↦ (pullback.fst (𝔸(n; S) ↘ S) g).appTop (coord S j.1)) fun _ ↦ linearForm g c

/-- `AlgebraicGeometry.AffineSpace.linearCoordHom` lies over `T`. -/
@[reassoc]
lemma linearCoordHom_over :
    linearCoordHom g c i ≫ 𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫
      𝔸({j // j ≠ i}; T) ↘ T = pullback.snd (𝔸(n; S) ↘ S) g := by
  rw [linearCoordHom, homOfVector_over_assoc, homOfVector_over]

/-- `AlgebraicGeometry.AffineSpace.linearCoordHom` pulls the coordinate of the affine line back
to the linear form. -/
lemma linearCoordHom_appTop_coord :
    (linearCoordHom g c i).appTop (coord _ PUnit.unit) = linearForm g c :=
  homOfVector_appTop_coord _ _ _

/-- `AlgebraicGeometry.AffineSpace.linearCoordHom` keeps the coordinates `xⱼ`, `j ≠ i`. -/
lemma linearCoordHom_over_appTop_coord (j : {j // j ≠ i}) :
    (linearCoordHom g c i ≫ 𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T)).appTop
      (coord T j) = (pullback.fst (𝔸(n; S) ↘ S) g).appTop (coord S j.1) := by
  rw [linearCoordHom, homOfVector_over, homOfVector_appTop_coord]

variable [DecidableEq n] {c i} (hc : IsUnit (c i))

/-- The coordinates of the inverse of `AlgebraicGeometry.AffineSpace.linearCoordHom` on
`𝔸¹(𝔸(n ∖ {i}; T))`, with coordinates `y` and `xⱼ`, `j ≠ i`: they are the `xⱼ` and
`xᵢ = cᵢ⁻¹ (y - ∑_{j ≠ i} cⱼ xⱼ)`. -/
noncomputable def linearCoordInvCoord (k : n) : Γ(𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)), ⊤) :=
  if h : k = i then
    (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫
      𝔸({j // j ≠ i}; T) ↘ T).appTop ((hc.unit⁻¹ : Γ(T, ⊤)ˣ) : Γ(T, ⊤)) *
    (coord _ PUnit.unit - ∑ j : {j // j ≠ i},
      (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T)).appTop (coord T j) *
      (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫
        𝔸({j // j ≠ i}; T) ↘ T).appTop (c j))
  else (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T)).appTop (coord T ⟨k, h⟩)

lemma linearCoordInvCoord_self : linearCoordInvCoord hc i =
    (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫
      𝔸({j // j ≠ i}; T) ↘ T).appTop ((hc.unit⁻¹ : Γ(T, ⊤)ˣ) : Γ(T, ⊤)) *
    (coord _ PUnit.unit - ∑ j : {j // j ≠ i},
      (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T)).appTop (coord T j) *
      (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫
        𝔸({j // j ≠ i}; T) ↘ T).appTop (c j)) :=
  dite_eq_left rfl

lemma linearCoordInvCoord_of_ne (j : {j // j ≠ i}) : linearCoordInvCoord hc j.1 =
    (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T)).appTop (coord T j) :=
  dite_eq_right j.2

/-- The inverse of `AlgebraicGeometry.AffineSpace.linearCoordHom`, when `cᵢ` is a unit:
`xᵢ = cᵢ⁻¹ (y - ∑_{j ≠ i} cⱼ xⱼ)`. -/
noncomputable def linearCoordInv :
    𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ⟶ pullback (𝔸(n; S) ↘ S) g :=
  pullback.lift
    (homOfVector (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫
      𝔸({j // j ≠ i}; T) ↘ T ≫ g) (linearCoordInvCoord hc))
    (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫ 𝔸({j // j ≠ i}; T) ↘ T)
    (by rw [homOfVector_over, Category.assoc])

@[reassoc]
lemma linearCoordInv_fst :
    linearCoordInv g hc ≫ pullback.fst (𝔸(n; S) ↘ S) g =
      homOfVector (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫
        𝔸({j // j ≠ i}; T) ↘ T ≫ g) (linearCoordInvCoord hc) :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma linearCoordInv_snd :
    linearCoordInv g hc ≫ pullback.snd (𝔸(n; S) ↘ S) g =
      𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫ 𝔸({j // j ≠ i}; T) ↘ T :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma linearCoordInv_hom : linearCoordInv g hc ≫ linearCoordHom g c i = 𝟙 _ := by
  refine hom_ext ?_ fun ⟨⟩ ↦ ?_
  · refine hom_ext ?_ fun j ↦ ?_
    · rw [Category.assoc, Category.assoc, linearCoordHom_over, linearCoordInv_snd,
        Category.id_comp]
    · rw [Category.assoc, linearCoordHom, homOfVector_over, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply, homOfVector_appTop_coord, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, linearCoordInv_fst, homOfVector_appTop_coord,
        linearCoordInvCoord_of_ne, Category.id_comp]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, linearCoordHom_appTop_coord,
      Scheme.Hom.id_appTop, CommRingCat.id_apply, linearForm, map_sum]
    simp only [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, linearCoordInv_fst,
      linearCoordInv_snd, homOfVector_appTop_coord]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i, linearCoordInvCoord_self]
    simp only [linearCoordInvCoord_of_ne]
    rw [mul_right_comm, ← map_mul, IsUnit.val_inv_mul, map_one, one_mul, sub_add_cancel]

@[reassoc (attr := simp)]
lemma linearCoordHom_inv : linearCoordHom g c i ≫ linearCoordInv g hc = 𝟙 _ := by
  refine pullback.hom_ext (hom_ext ?_ fun k ↦ ?_) ?_
  · rw [Category.assoc, Category.assoc, linearCoordInv_fst_assoc, homOfVector_over,
      linearCoordHom_over_assoc, Category.id_comp, pullback.condition]
  · rw [Category.assoc, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, linearCoordInv_fst,
      homOfVector_appTop_coord, Category.id_comp]
    by_cases h : k = i
    · subst h
      rw [linearCoordInvCoord_self, map_mul, map_sub, map_sum, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, linearCoordHom_over, linearCoordHom_appTop_coord, linearForm,
        Fintype.sum_eq_add_sum_subtype_ne _ k]
      simp only [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        linearCoordHom_over, linearCoordHom_over_appTop_coord]
      rw [add_sub_cancel_right, mul_left_comm, ← map_mul, IsUnit.val_inv_mul, map_one, mul_one]
    · rw [linearCoordInvCoord_of_ne hc ⟨k, h⟩, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, linearCoordHom_over_appTop_coord]
  · rw [Category.assoc, linearCoordInv_snd, linearCoordHom_over, Category.id_comp]

omit [DecidableEq n] in
/-- The change of variables `AlgebraicGeometry.AffineSpace.linearCoordHom` is an isomorphism
when the coefficient `cᵢ` is a unit. -/
lemma isIso_linearCoordHom {c : n → Γ(T, ⊤)} {i : n} (hc : IsUnit (c i)) :
    IsIso (linearCoordHom g c i) := by
  classical
  exact ⟨linearCoordInv g hc, linearCoordHom_inv g hc, linearCoordInv_hom g hc⟩

/-- The inverse change of variables `AlgebraicGeometry.AffineSpace.linearCoordInv` is an
isomorphism. -/
lemma isIso_linearCoordInv : IsIso (linearCoordInv g hc) :=
  ⟨linearCoordHom g c i, linearCoordInv_hom g hc, linearCoordHom_inv g hc⟩

end AlgebraicGeometry.AffineSpace
