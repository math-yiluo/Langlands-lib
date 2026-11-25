/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Pairing

/-!
# Perfectness of the derived Poincaré pairing for every complex

At a finite coefficient ring the derived Poincaré pairing

`β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`

is perfect for `K` dualizable (`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`). The
only place where dualizability of `K` enters is the identification of `K^∨ ⊗ᴸ T` with the
internal hom `RHom(K, T)`. When the twist `T` is invertible, as the Tate twist `Λ_X(d)` is, this
identification holds for every `K`, so the derived Poincaré pairing is perfect for every `K`.

## Main statements

- `CategoryTheory.MonoidalClosed.isIso_ihomUnitTensorToIhom_of_isInvertible`: the comparison map
  `(ihom X).obj (𝟙_ C) ⊗ N ⟶ (ihom X).obj N` is an isomorphism for `N` invertible.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isInvertible`: at a finite
  coefficient ring, `β_K` is perfect for every `K` as soon as the twist `T` is invertible.
- `AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing_of_finite`: the
  derived Poincaré pairing of a Tate orientation is perfect for every `K`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

/-- The comparison map `ihomUnitTensorToIhom X N` factors through
`ihomTensorToIhom X (𝟙_ C) N` and the left unitor of `N`. -/
lemma ihomUnitTensorToIhom_eq_ihomTensorToIhom_comp (X N : C) :
    ihomUnitTensorToIhom X N = ihomTensorToIhom X (𝟙_ C) N ≫ (ihom X).map (λ_ N).hom := by
  rw [ihomUnitTensorToIhom, ihomTensorToIhom, ← curry_natural_right, Category.assoc]

/-- The comparison map `(ihom X).obj (𝟙_ C) ⊗ N ⟶ (ihom X).obj N` is an isomorphism when `N` is
invertible, whatever `X`. -/
theorem isIso_ihomUnitTensorToIhom_of_isInvertible (X : C) {N : C} (hN : IsInvertible N) :
    IsIso (ihomUnitTensorToIhom X N) := by
  rw [ihomUnitTensorToIhom_eq_ihomTensorToIhom_comp]
  have := isIso_ihomTensorToIhom X (𝟙_ C) hN
  infer_instance

end CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

namespace Etale

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a] {d : ℕ}
  {G : 𝐃(Y, A) ⥤ 𝐃(X, A)} (adj : R(a)_![A] ⊣ G)

section Perfectness

omit [ConcreteCategory A FA] [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] in
/-- If the comparison map `K^∨ ⊗ᴸ T ⟶ RHom(K, T)` is an isomorphism, the twisted evaluation
`K ⊗ᴸ (K^∨ ⊗ᴸ T) ⟶ T` is a counit: every map `K ⊗ᴸ Z ⟶ T` factors uniquely as `K ⊗ᴸ y` followed
by the twisted evaluation. -/
theorem bijective_derivedTensor_map_comp_twistedEvaluation_of_isIso
    {T K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hi : IsIso (MonoidalClosed.ihomUnitTensorToIhom K T))
    (Z : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Function.Bijective (fun y : Z ⟶ ((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T ↦
      ((derivedTensor A X).obj K).map y ≫ twistedEvaluation T K) := by
  have ht : twistedEvaluation T K =
      MonoidalClosed.uncurry (MonoidalClosed.ihomUnitTensorToIhom K T) := by
    rw [MonoidalClosed.ihomUnitTensorToIhom, MonoidalClosed.uncurry_curry]
    rfl
  have he : (fun y : Z ⟶ ((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T ↦
      ((derivedTensor A X).obj K).map y ≫ twistedEvaluation T K) =
      MonoidalClosed.uncurry ∘ (fun y ↦ y ≫ MonoidalClosed.ihomUnitTensorToIhom K T) := by
    funext y
    rw [ht]
    exact (MonoidalClosed.uncurry_natural_left _ _).symm
  rw [he]
  exact Function.Bijective.comp ⟨MonoidalClosed.uncurry_injective,
    fun g ↦ ⟨MonoidalClosed.curry g, MonoidalClosed.uncurry_curry g⟩⟩
    ((isIso_iff_yoneda_map_bijective _).1 hi _)

omit [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A] [HasCompactification a] in
/-- The adjoint description of the evaluation part of the derived Poincaré pairing, when the
comparison map `K^∨ ⊗ᴸ T ⟶ RHom(K, T)` is an isomorphism: maps `h : N ⟶ Ra_*(K^∨ ⊗ᴸ T)`
correspond bijectively to maps `K ⊗ᴸ La^* N ⟶ T`. -/
theorem bijective_derivedTensor_map_comp_counit_comp_twistedEvaluation_of_isIso
    {T K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hi : IsIso (MonoidalClosed.ihomUnitTensorToIhom K T))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Function.Bijective (fun h : N ⟶ (R((a)_*[A])).obj (((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T) ↦
      ((derivedTensor A X).obj K).map ((L((a)^*[A])).map h) ≫
        ((derivedTensor A X).obj K).map ((derivedUpperStarLowerStarAdjunction A a).counit.app _) ≫
          twistedEvaluation T K) := by
  have e : (fun h : N ⟶ (R((a)_*[A])).obj (((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T) ↦
      ((derivedTensor A X).obj K).map ((L((a)^*[A])).map h) ≫
        ((derivedTensor A X).obj K).map ((derivedUpperStarLowerStarAdjunction A a).counit.app _) ≫
          twistedEvaluation T K) =
      (fun y ↦ ((derivedTensor A X).obj K).map y ≫ twistedEvaluation T K) ∘
        ((derivedUpperStarLowerStarAdjunction A a).homEquiv _ _).symm := by
    funext h
    simp [Adjunction.homEquiv_counit]
  rw [e]
  exact (bijective_derivedTensor_map_comp_twistedEvaluation_of_isIso A hi _).comp
    (Equiv.bijective _)

omit [HasSmallSiteSheafify A] in
/-- The derived Poincaré pairing `β_K` is perfect as soon as the comparison map
`K^∨ ⊗ᴸ T ⟶ RHom(K, T)` is an isomorphism and the projection formula holds at a class of test
objects detecting isomorphisms after the shift by `2d`. This is
`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting` with the
dualizability of `K` replaced by its only consequence used in the proof. -/
theorem isPerfectPairing_poincarePairing_of_isDetecting_of_isIso {T : 𝐃(X, A)}
    (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hi : IsIso (MonoidalClosed.ihomUnitTensorToIhom K T))
    (S : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) → Prop)
    (hS : ∀ ⦃P Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)⦄ (u : P ⟶ Q),
      (∀ N, S N → Function.Bijective (fun g : N⟦(2 * d : ℤ)⟧ ⟶ P ↦ g ≫ u)) → IsIso u)
    (hPF : ∀ N, S N → HasProjectionFormula A a K N) :
    IsPerfectPairing (poincarePairing adj γ K) := by
  constructor
  rw [poincarePairing, poincarePairingEvaluation, mixedSupportCupProduct]
  exact MonoidalClosed.isIso_curry_of_projection _ _ _ _ _ _ _ _ _ S hS hPF
    (bijective_derivedTensor_map_comp_counit_comp_twistedEvaluation_of_isIso A a hi)
    (bijective_rightDerivedLowerShriek_map_shift_comp_smoothTrace A a adj γ)

omit [HasSmallSiteSheafify A] in
/-- The derived Poincaré pairing `β_K` is perfect for every `K` at which the projection formula
holds against every object, as soon as the twist `T` is invertible. -/
theorem isPerfectPairing_poincarePairing_of_isInvertible_of_hasProjectionFormula {T : 𝐃(X, A)}
    (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _)) (hT : IsInvertible T)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hPF : ∀ N, HasProjectionFormula A a K N) :
    IsPerfectPairing (poincarePairing adj γ K) :=
  isPerfectPairing_poincarePairing_of_isDetecting_of_isIso A a adj γ
    (MonoidalClosed.isIso_ihomUnitTensorToIhom_of_isInvertible K hT) (fun _ ↦ True)
    (fun _ _ u hu ↦ isIso_of_bijective_comp_shift (2 * d : ℤ) u fun N ↦ hu N trivial)
    (fun N _ ↦ hPF N)

end Perfectness

section ModuleCat

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **The derived Poincaré pairing is perfect for every complex when the twist is invertible.**
For a finite coefficient ring `Λ`, a purity isomorphism `γ : T[2d] ≅ Ra^! Λ_Y` with `T`
invertible (as the Tate twist `Λ_X(d)` is), and every `K ∈ D(X_ét, Λ)`, the derived Poincaré
pairing `β_K` is perfect: its adjoint `(Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨` is an isomorphism.
Indeed `K^∨ ⊗ᴸ T ≅ RHom(K, T)` for `T` invertible
(`CategoryTheory.MonoidalClosed.isIso_ihomUnitTensorToIhom_of_isInvertible`), which is the only
use of the dualizability of `K` in `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`. -/
theorem isPerfectPairing_poincarePairing_of_isInvertible {T : DerivedCategoryModule Λ X}
    (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a) (hT : IsInvertible T)
    (K : DerivedCategoryModule Λ X) :
    IsPerfectPairing (poincarePairing (rightDerivedUpperShriekAdjunction Λ a) γ K) :=
  isPerfectPairing_poincarePairing_of_isInvertible_of_hasProjectionFormula _ a _ γ hT fun N ↦
    hasProjectionFormula_of_finite Λ a K N

end ModuleCat

namespace TateOrientation

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {a}

/-- **The derived Poincaré pairing of a Tate orientation is perfect for every complex.** At a
finite coefficient ring `Λ`, the derived Poincaré pairing
`β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨(d)))[2d] ⟶ Λ_Y` of a Tate orientation `γ` is perfect for every
`K ∈ D(X_ét, Λ)`, the Tate twist `Λ_X(d)` being invertible. For `K` dualizable this is
`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing`. -/
theorem isPerfectPairing_poincarePairing_of_finite [HasInvertibleExponent Λ X]
    (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) :
    IsPerfectPairing (γ.poincarePairing K) :=
  Etale.isPerfectPairing_poincarePairing_of_isInvertible a Λ _
    ((isInvertible_iff_exists_derivedTensor _).2 (isInvertible_tateObject Λ X d)) K

end TateOrientation

end Etale

end AlgebraicGeometry
