/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion

/-!
# Reduction modulo an ideal on the derived category of sheaves of modules

Let `(C, J)` be an essentially small site and `R` a commutative ring. For an ideal `𝔞` of `R`,
the reduction `K ↦ K ⊗ᴸ R/𝔞` (`DerivedCategory.reductionModIdeal J 𝔞`) is a triangulated
endofunctor of `D(J, R)`. For a nonzerodivisor `ϖ`:

* if `K ⊗ᴸ R/ϖ = 0`, then `ϖ` acts invertibly on `K`
  (`DerivedCategory.isIso_smul_id_of_isZero_reductionModIdeal`);
* a morphism whose reduction modulo `ϖ` is an isomorphism becomes an isomorphism after derived
  `ϖ`-completion (`DerivedCategory.isIso_derivedCompletion_map_of_isIso_reductionModIdeal`).

## Implementation notes

The monoidal structure of `D(J, R)` is taken from the fields of
`DerivedCategory.sheafTensorStructure J R`, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high) :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

noncomputable local instance (priority := high) :
    MonoidalPreadditive (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalPreadditive

noncomputable local instance (priority := high) :
    MonoidalLinear R (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalLinear

noncomputable local instance (priority := high) :
    (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J R).commShift₂

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorLeft K

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorRight K

/-- Reduction of coefficients along a quotient of the coefficient ring: the functor
`K ↦ K ⊗ᴸ (R/𝔞)` on `D(J, R)`, where `R/𝔞` is the constant sheaf placed in degree `0`. For
`R = 𝒪_E` and `𝔞 = 𝔪_Eⁿ` this is the finite reduction `K ↦ K_n` of the adic formalism. -/
noncomputable def reductionModIdeal (𝔞 : Ideal R) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj
    ((singleFunctor _ 0).obj ((constantSheaf J (ModuleCat.{u + 1} R)).obj
      (ModuleCat.of R (R ⧸ 𝔞))))

/-- The reduction `K ↦ K ⊗ᴸ (R/𝔞)` commutes with shifts. -/
noncomputable instance (𝔞 : Ideal R) : (reductionModIdeal J 𝔞).CommShift ℤ :=
  Functor.CommShift₂.commShiftFlipObj (h := .int) _

/-- The reduction `K ↦ K ⊗ᴸ (R/𝔞)` is triangulated. -/
instance (𝔞 : Ideal R) : (reductionModIdeal J 𝔞).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorRight _

variable {J}

/-- **Reduction modulo `ϖ` detects invertibility of `ϖ`.** For a nonzerodivisor `ϖ` of `R` and
`K ∈ D(J, R)`, if the reduction `K ⊗ᴸ R/ϖ` vanishes then `ϖ` acts invertibly on `K`: tensoring
the distinguished triangle `R ⟶ R ⟶ R/ϖ ⟶ R⟦1⟧` (the first map being the multiplication by `ϖ`)
with `K` gives a distinguished triangle `K ⟶ K ⟶ 0 ⟶ K⟦1⟧` whose first map is the
multiplication by `ϖ`. -/
theorem isIso_smul_id_of_isZero_reductionModIdeal {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    (hK : IsZero ((reductionModIdeal J (Ideal.span {ϖ})).obj K)) :
    IsIso (ϖ • 𝟙 K) := by
  let T := tensorQuotPowTriangle hϖ rfl K 1
  have hT : T ∈ distTriang _ := tensorQuotPowTriangle_distinguished hϖ rfl K 1
  -- the third vertex of the tensored triangle is the reduction of `K` modulo `ϖ`
  let e : (Ideal.quotPowFunctor (Ideal.span {ϖ})).obj (op 1) ≅
      ModuleCat.of R (R ⧸ Ideal.span {ϖ}) :=
    (Submodule.quotEquivOfEq _ _ (pow_one _)).toModuleIso
  have h₃ : IsZero T.obj₃ :=
    hK.of_iso (whiskerLeftIso K ((singleFunctor _ 0).mapIso
      ((constantSheaf J (ModuleCat.{u + 1} R)).mapIso e)))
  have h₁ : IsIso T.mor₁ := (Triangle.isZero₃_iff_isIso₁ _ hT).1 h₃
  let S := (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).obj
    (𝟙_ (Sheaf J (ModuleCat.{u + 1} R)))
  have h₂ : IsIso (K ◁ (ϖ • 𝟙 S)) := by
    have e : K ◁ (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
        ((constantSheaf J (ModuleCat.{u + 1} R)).map (ϖ ^ 1 • 𝟙 (𝟙_ (ModuleCat.{u + 1} R)))) =
        K ◁ (ϖ • 𝟙 S) := by
      rw [pow_one, Functor.map_smul, Functor.map_smul, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id]
      rfl
    rw [← e]
    exact h₁
  rw [MonoidalLinear.whiskerLeft_smul, MonoidalCategory.whiskerLeft_id] at h₂
  have : ϖ • 𝟙 K = (unitIso K).hom ≫ (ϖ • 𝟙 _) ≫ (unitIso K).inv := by
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.hom_inv_id]
  rw [this]
  exact inferInstanceAs (IsIso ((unitIso K).hom ≫ (ϖ • 𝟙 (K ⊗ S)) ≫ (unitIso K).inv))

/-- **The derived completion inverts morphisms whose reduction is an isomorphism.** A morphism
`u` of `D(J, R)` whose reduction modulo a nonzerodivisor `ϖ` is an isomorphism becomes an
isomorphism after derived `ϖ`-completion: its cone `C` has `C ⊗ᴸ R/ϖ = 0`, so `ϖ` acts
invertibly on `C`, and the derived completion inverts such morphisms. -/
theorem isIso_derivedCompletion_map_of_isIso_reductionModIdeal {ϖ : R}
    (hϖ : ϖ ∈ nonZeroDivisors R) {M N : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (u : M ⟶ N) (hu : IsIso ((reductionModIdeal J (Ideal.span {ϖ})).map u)) :
    IsIso ((derivedCompletion J (Ideal.span {ϖ}) ⟨ϖ, hϖ, rfl⟩).map u) := by
  obtain ⟨C', g, h, hT⟩ := distinguished_cocone_triangle u
  have hC : IsZero ((reductionModIdeal J (Ideal.span {ϖ})).obj C') :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((reductionModIdeal J (Ideal.span {ϖ})).map_distinguished _ hT)).2 hu
  exact isIso_derivedCompletion_map _ rfl hT
    (isIso_smul_id_of_isZero_reductionModIdeal hϖ C' hC)

end DerivedCategory
