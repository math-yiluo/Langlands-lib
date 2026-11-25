/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.TripleProj

/-!
# Subtraction on relative affine space and the fibres over the origin

The subtraction `(x, y) ↦ x - y` of `𝔸(n; S)` (`AlgebraicGeometry.AffineSpace.sub`) and the
automorphism `1 × ι : (x, y) ↦ (x, -y)` of `𝔸(n; S) ×_S 𝔸(n; S)`
(`AlgebraicGeometry.AffineSpace.prodNeg`). The fibre of the subtraction over the zero section
is the diagonal, and the fibre of the addition over the zero section is the antidiagonal
`x ↦ (x, -x)`.

On the triple product `𝔸(n; S) ×_S 𝔸(n; S) ×_S 𝔸(n; S)` with points `(x, ξ, y)`, the shear
`(x, ξ, y) ↦ (ξ, x ∓ y)` (`CategoryTheory.Limits.pullback.tripleShear`) pulls the standard
pairing back to `⟨ξ, x ∓ y⟩ = ⟨x, ξ⟩ ∓ ⟨ξ, y⟩`.

## Main statements

- `AlgebraicGeometry.AffineSpace.isPullback_diagonal_sub`: `Δ` is the base change of the zero
  section along the subtraction.
- `AlgebraicGeometry.AffineSpace.isPullback_diagonal_prodNeg_add`: `(1 × ι) ∘ Δ` is the base
  change of the zero section along the addition.
- `AlgebraicGeometry.AffineSpace.tripleShear_sub_appTop_stdPairing` and
  `AlgebraicGeometry.AffineSpace.tripleShear_add_appTop_stdPairing`: the pullbacks of the
  standard pairing along the shears.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineSpace

variable (n : Type u) (S : Scheme.{u})

set_option hygiene false in
/-- The first projection `𝔸(n; S) ×_S 𝔸(n; S) ⟶ 𝔸(n; S)`. -/
local notation "pr₁" => Limits.pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)

set_option hygiene false in
/-- The second projection `𝔸(n; S) ×_S 𝔸(n; S) ⟶ 𝔸(n; S)`. -/
local notation "pr₂" => Limits.pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)

/-- The subtraction `(x, y) ↦ x - y` of `𝔸(n; S)`, a morphism
`𝔸(n; S) ×_S 𝔸(n; S) ⟶ 𝔸(n; S)`. -/
noncomputable def sub : pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) ⟶ 𝔸(n; S) :=
  homOfVector (pr₁ ≫ 𝔸(n; S) ↘ S) fun i ↦ (pr₁).appTop (coord S i) - (pr₂).appTop (coord S i)

@[reassoc (attr := simp)]
lemma sub_over : sub n S ≫ 𝔸(n; S) ↘ S = pr₁ ≫ 𝔸(n; S) ↘ S :=
  homOfVector_over _ _

@[simp]
lemma sub_appTop_coord (i : n) :
    (sub n S).appTop (coord S i) = (pr₁).appTop (coord S i) - (pr₂).appTop (coord S i) :=
  homOfVector_appTop_coord _ _ _

/-- The automorphism `1 × ι : (x, y) ↦ (x, -y)` of `𝔸(n; S) ×_S 𝔸(n; S)`. -/
noncomputable def prodNeg : pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) ⟶
    pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) :=
  pullback.map _ _ _ _ (𝟙 _) (neg n S) (𝟙 S) (by simp) (by simp [neg_over])

@[reassoc (attr := simp)]
lemma prodNeg_fst : prodNeg n S ≫ pr₁ = pr₁ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma prodNeg_snd : prodNeg n S ≫ pr₂ = pr₂ ≫ neg n S :=
  pullback.lift_snd _ _ _

/-- The diagonal of `𝔸(n; S)` is the fibre of the subtraction over the zero section:

```
         π
  𝔸(n; S) ────▶ S
     │          │
    Δ│          │0
     ▼          ▼
  𝔸(n; S)² ──▶ 𝔸(n; S)
          sub
```
-/
theorem isPullback_diagonal_sub :
    IsPullback (𝔸(n; S) ↘ S) (pullback.diagonal (𝔸(n; S) ↘ S)) (zeroSection n S) (sub n S) := by
  have hc : (𝔸(n; S) ↘ S) ≫ zeroSection n S = pullback.diagonal (𝔸(n; S) ↘ S) ≫ sub n S := by
    refine hom_ext ?_ fun i ↦ ?_
    · simp
    · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, zeroSection_appTop_coord,
        map_zero, sub_appTop_coord, map_sub]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop, pullback.diagonal_fst, pullback.diagonal_snd, sub_self]
  refine ⟨⟨hc⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ s.snd ≫ pr₁) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s l hl₁ hl₂ ↦ ?_)⟩⟩
  · rw [Category.assoc, ← sub_over, ← Category.assoc, ← s.condition, Category.assoc,
      zeroSection_over, Category.comp_id]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      refine hom_ext ?_ fun i ↦ ?_
      · rw [Category.assoc, Category.assoc, pullback.condition]
      · have h := congrArg (fun a ↦ a.appTop (coord S i)) s.condition
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, zeroSection_appTop_coord,
          map_zero, sub_appTop_coord, map_sub] at h
        exact sub_eq_zero.1 h.symm
  · rw [← hl₂, Category.assoc, pullback.diagonal_fst, Category.comp_id]

@[reassoc (attr := simp)]
lemma prodNeg_prodNeg : prodNeg n S ≫ prodNeg n S = 𝟙 _ := by
  ext <;> simp [neg_comp_neg]

instance : IsIso (prodNeg n S) := ⟨prodNeg n S, prodNeg_prodNeg n S, prodNeg_prodNeg n S⟩

/-- Adding `-y` is subtracting `y`: `(1 × ι) ≫ add = sub`. -/
@[reassoc (attr := simp)]
lemma prodNeg_add : prodNeg n S ≫ add n S = sub n S := by
  refine hom_ext ?_ fun i ↦ ?_
  · simp
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, add_appTop_coord, map_add,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, prodNeg_fst, prodNeg_snd, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, neg_appTop_coord, map_neg, sub_appTop_coord, sub_eq_add_neg]

/-- The antidiagonal `x ↦ (x, -x)` of `𝔸(n; S)`, written `(1 × ι) ∘ Δ`, is the fibre of the
addition over the zero section. -/
theorem isPullback_diagonal_prodNeg_add :
    IsPullback (𝔸(n; S) ↘ S) (pullback.diagonal (𝔸(n; S) ↘ S) ≫ prodNeg n S) (zeroSection n S)
      (add n S) :=
  (isPullback_diagonal_sub n S).of_iso (Iso.refl _) (Iso.refl _) (asIso (prodNeg n S))
    (Iso.refl _) (by simp) (by simp) (by simp) (by simp)


/-- Equal composites of morphisms of schemes act equally on global sections. -/
private lemma appTop_appTop_eq_of_comp_eq {X Y Y' Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X ⟶ Y'} {g' : Y' ⟶ Z} (w : f ≫ g = f' ≫ g') (x : Γ(Z, ⊤)) :
    f.appTop (g.appTop x) = f'.appTop (g'.appTop x) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, w, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]

section Triple

variable [Fintype n]

set_option hygiene false in
/-- The projection `(x, ξ, y) ↦ (x, ξ)` of the triple product. -/
local notation "r₁₂" => Limits.pullback.fst (pr₂) (pr₁)

set_option hygiene false in
/-- The projection `(x, ξ, y) ↦ (ξ, y)` of the triple product. -/
local notation "r₂₃" => Limits.pullback.snd (pr₂) (pr₁)

set_option hygiene false in
/-- The projection `(x, ξ, y) ↦ (x, y)` of the triple product. -/
local notation "r₁₃" =>
  Limits.pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)

/-- The shear `(x, ξ, y) ↦ (ξ, x - y)` pulls the standard pairing back to
`⟨ξ, x - y⟩ = ⟨x, ξ⟩ - ⟨ξ, y⟩`. -/
lemma tripleShear_sub_appTop_stdPairing :
    (pullback.tripleShear (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (sub_over n S)).appTop
        (stdPairing n S) =
      (r₁₂).appTop (stdPairing n S) - (r₂₃).appTop (stdPairing n S) := by
  simp only [stdPairing, map_sum, map_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [appTop_appTop_eq_of_comp_eq (pullback.tripleShear_fst _ _ _ _),
    appTop_appTop_eq_of_comp_eq (pullback.tripleShear_snd _ _ _ _), sub_appTop_coord, map_sub,
    appTop_appTop_eq_of_comp_eq (pullback.tripleProj₁₃_fst _ _ _),
    appTop_appTop_eq_of_comp_eq (pullback.tripleProj₁₃_snd _ _ _),
    appTop_appTop_eq_of_comp_eq (pullback.condition (f := pr₂) (g := pr₁)).symm]
  ring

/-- The shear `(x, ξ, y) ↦ (ξ, x + y)` pulls the standard pairing back to
`⟨ξ, x + y⟩ = ⟨x, ξ⟩ + ⟨ξ, y⟩`. -/
lemma tripleShear_add_appTop_stdPairing :
    (pullback.tripleShear (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (add_over n S)).appTop
        (stdPairing n S) =
      (r₁₂).appTop (stdPairing n S) + (r₂₃).appTop (stdPairing n S) := by
  simp only [stdPairing, map_sum, map_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [appTop_appTop_eq_of_comp_eq (pullback.tripleShear_fst _ _ _ _),
    appTop_appTop_eq_of_comp_eq (pullback.tripleShear_snd _ _ _ _), add_appTop_coord, map_add,
    appTop_appTop_eq_of_comp_eq (pullback.tripleProj₁₃_fst _ _ _),
    appTop_appTop_eq_of_comp_eq (pullback.tripleProj₁₃_snd _ _ _),
    appTop_appTop_eq_of_comp_eq (pullback.condition (f := pr₂) (g := pr₁)).symm]
  ring

end Triple

end AlgebraicGeometry.AffineSpace
