/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso

/-!
# Degree-zero parts of perfect pairings

Let `b : C ⊗ᴸ D ⟶ Λ_X` be a perfect pairing in `D(X_ét, A)` and `i + j = 0`. The degree-zero
part of `b` pairs a class `x : Λ_X ⟶ C[i]` with a class `y : Λ_X ⟶ D[j]`. This file shows that
it is the composition pairing `⟨x, y⟩ = x ≫ g(y)` for an additive bijection
`g : Hom(Λ_X, D[j]) ≃ Hom(C[i], Λ_X)`.

## Main statements

- `AlgebraicGeometry.Etale.isPerfectPairing_iff_bijective`: `b` is perfect if and only if
  `y ↦ (C ⊗ᴸ y) ≫ b` is bijective on `Hom(S, D)` for every `S`.
- `AlgebraicGeometry.Etale.IsPerfectPairing.shift`: the shifted pairing
  `C[i] ⊗ᴸ D[j] ≅ (C ⊗ᴸ D)[i + j] ⟶ Λ_X[i + j] ≅ Λ_X` is perfect for `i + j = 0`.
- `AlgebraicGeometry.Etale.IsPerfectPairing.exists_addEquiv_degreeZero`: the degree-zero part of
  a perfect pairing is a composition pairing `x ≫ g(y)` with `g` an additive bijection.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry

namespace Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

/-- A pairing `b : C ⊗ᴸ D ⟶ Λ_X` is perfect if and only if, for every `S`, every morphism
`C ⊗ᴸ S ⟶ Λ_X` is `(C ⊗ᴸ y) ≫ b` for a unique `y : S ⟶ D`. -/
lemma isPerfectPairing_iff_bijective {C D : 𝐃(X, A)}
    (b : ((derivedTensor A X).obj C).obj D ⟶ 𝟙_ _) :
    IsPerfectPairing b ↔ ∀ S : 𝐃(X, A),
      Function.Bijective (fun y : S ⟶ D ↦ ((derivedTensor A X).obj C).map y ≫ b) := by
  have key : ∀ S : 𝐃(X, A), (fun y : S ⟶ D ↦ y ≫ curry b) =
      curry ∘ (fun y : S ⟶ D ↦ ((derivedTensor A X).obj C).map y ≫ b) := fun S ↦ by
    funext y
    exact (curry_natural_left y b).symm
  rw [isPerfectPairing_iff]
  refine ⟨fun ⟨h⟩ S ↦ ?_, fun h ↦ ⟨(isIso_iff_yoneda_map_bijective _).2 fun S ↦ ?_⟩⟩
  · have := (isIso_iff_yoneda_map_bijective _).1 h S
    rw [key] at this
    exact (Function.Bijective.of_comp_iff' ((ihom.adjunction C).homEquiv _ _).bijective _).1 this
  · rw [key]
    exact ((ihom.adjunction C).homEquiv _ _).bijective.comp (h S)

/-- The shift of a perfect pairing `b : C ⊗ᴸ D ⟶ Λ_X` by `i + j = 0`,
```
                  ≅                     b[i + j]                 ≅
C[i] ⊗ᴸ D[j] ─────▶ (C ⊗ᴸ D)[i + j] ──────────▶ Λ_X[i + j] ─────▶ Λ_X,
```
is perfect. -/
lemma IsPerfectPairing.shift {C D : 𝐃(X, A)} {b : ((derivedTensor A X).obj C).obj D ⟶ 𝟙_ _}
    (hb : IsPerfectPairing b) (i j : ℤ) (h : i + j = 0) :
    IsPerfectPairing ((derivedTensorShiftIso A C D i j).hom ≫ b⟦i + j⟧' ≫
      (shiftFunctorZero' _ (i + j) h).hom.app _) := by
  rw [isPerfectPairing_iff_bijective] at hb ⊢
  intro T
  let S := T⟦-j⟧
  let ε : S⟦j⟧ ≅ T := (shiftFunctorCompIsoId _ (-j) j (neg_add_cancel j)).app T
  let κ : ((derivedTensor A X).obj (C⟦i⟧)).obj T ⟶ ((derivedTensor A X).obj C).obj S :=
    ((derivedTensor A X).obj (C⟦i⟧)).map ε.inv ≫ (derivedTensorShiftIso A C S i j).hom ≫
      (shiftFunctorZero' _ (i + j) h).hom.app _
  have : IsIso κ := by dsimp [κ]; infer_instance
  have hshift : Function.Bijective (fun y : S ⟶ D ↦ ε.inv ≫ y⟦j⟧') := by
    convert (Iso.homCongr ε (Iso.refl (D⟦j⟧))).bijective.comp
      ⟨(shiftFunctor _ j).map_injective, (shiftFunctor _ j).map_surjective⟩ using 1
    funext y
    simp [Iso.homCongr_apply]
  have hcomp : (fun y : T ⟶ D⟦j⟧ ↦ ((derivedTensor A X).obj (C⟦i⟧)).map y ≫
      (derivedTensorShiftIso A C D i j).hom ≫ b⟦i + j⟧' ≫
        (shiftFunctorZero' _ (i + j) h).hom.app _) ∘ (fun y : S ⟶ D ↦ ε.inv ≫ y⟦j⟧') =
      (fun f ↦ κ ≫ f) ∘ (fun y : S ⟶ D ↦ ((derivedTensor A X).obj C).map y ≫ b) := by
    funext y
    simp only [Function.comp_apply, κ, Functor.map_comp, Category.assoc]
    rw [derivedTensorShiftIso_hom_naturality_right_assoc, ← Functor.map_comp_assoc]
    erw [(shiftFunctorZero' _ (i + j) h).hom.naturality]
    rfl
  rw [← Function.Bijective.of_comp_iff _ hshift, hcomp]
  have hκ : Function.Bijective (fun f : ((derivedTensor A X).obj C).obj S ⟶ 𝟙_ _ ↦ κ ≫ f) :=
    ⟨fun f g hfg ↦ (cancel_epi κ).1 hfg, fun f ↦ ⟨inv κ ≫ f, by simp⟩⟩
  exact hκ.comp (hb S)

/-- **The degree-zero part of a perfect pairing is a composition pairing.** Let
`b : C ⊗ᴸ D ⟶ Λ_X` be perfect and `i + j = 0`. The degree-zero part of `b` on classes
`x : Λ_X ⟶ C[i]` and `y : Λ_X ⟶ D[j]`,
```
      λ⁻¹               x ⊗ y                   ≅                    b[i + j]           ≅
Λ_X ─────▶ Λ_X ⊗ᴸ Λ_X ────────▶ C[i] ⊗ᴸ D[j] ─────▶ (C ⊗ᴸ D)[i + j] ──────────▶ Λ_X[i + j] ───▶ Λ_X,
```
is `x ≫ g(y)` for an additive bijection `g : Hom(Λ_X, D[j]) ≃ Hom(C[i], Λ_X)`. -/
lemma IsPerfectPairing.exists_addEquiv_degreeZero {C D : 𝐃(X, A)}
    {b : ((derivedTensor A X).obj C).obj D ⟶ 𝟙_ _} (hb : IsPerfectPairing b) (i j : ℤ)
    (h : i + j = 0) :
    ∃ g : ((𝟙_ 𝐃(X, A)) ⟶ D⟦j⟧) ≃+ (C⟦i⟧ ⟶ 𝟙_ 𝐃(X, A)), ∀ x y,
      (derivedTensorLeftUnitor A X (𝟙_ _)).inv ≫ ((derivedTensor A X).flip.obj (𝟙_ _)).map x ≫
        ((derivedTensor A X).obj (C⟦i⟧)).map y ≫ (derivedTensorShiftIso A C D i j).hom ≫
          b⟦i + j⟧' ≫ (shiftFunctorZero' _ (i + j) h).hom.app _ = x ≫ g y := by
  have hb' := (isPerfectPairing_iff_bijective _).1 (hb.shift i j h) (𝟙_ _)
  let b' := (derivedTensorShiftIso A C D i j).hom ≫ b⟦i + j⟧' ≫
    (shiftFunctorZero' _ (i + j) h).hom.app (𝟙_ 𝐃(X, A))
  let g₀ : ((𝟙_ 𝐃(X, A)) ⟶ D⟦j⟧) →+ (C⟦i⟧ ⟶ 𝟙_ 𝐃(X, A)) :=
    { toFun := fun y ↦ (derivedTensorRightUnitor A X (C⟦i⟧)).inv ≫
        ((derivedTensor A X).obj (C⟦i⟧)).map y ≫ b'
      map_zero' := by simp
      map_add' := fun y y' ↦ by
        simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add] }
  have hg₀ : Function.Bijective g₀ := by
    convert (Iso.homCongr (derivedTensorRightUnitor A X (C⟦i⟧)) (Iso.refl _)).bijective.comp
      hb' using 1
    funext y
    simp [Iso.homCongr_apply, g₀, b']
  refine ⟨AddEquiv.ofBijective g₀ hg₀, fun x y ↦ ?_⟩
  change (λ_ _).inv ≫ x ▷ 𝟙_ _ ≫ _ = x ≫ (ρ_ (C⟦i⟧)).inv ≫ _
  rw [unitors_inv_equal, ← rightUnitor_inv_naturality_assoc]

end Etale

end AlgebraicGeometry
