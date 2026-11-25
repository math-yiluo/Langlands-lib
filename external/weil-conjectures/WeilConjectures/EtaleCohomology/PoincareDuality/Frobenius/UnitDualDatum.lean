/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UnitPairing
public import WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.WeilDual
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# The contragredient datum of the unit

For an endomorphism `g` of a scheme `X`, the constant complex `Λ_X` carries its canonical Weil
datum `ε : Lg^* Λ_X ≅ Λ_X`. Its coefficient dual `Λ_X^∨ = RHom(Λ_X, Λ_X)` carries the
contragredient datum `φ_{Λ^∨}` (`AlgebraicGeometry.Etale.contragredientWeilDatum`). We show that
the canonical identification `Λ_X^∨ ≅ Λ_X` (`AlgebraicGeometry.Etale.coefficientDualUnitIso`) is a
morphism of Weil objects from `(Λ_X^∨, φ_{Λ^∨})` to `(Λ_X, ε)`
(`AlgebraicGeometry.Etale.isWeilMorphism_coefficientDualUnitIso_hom`), so that the Frobenius
operators, and those of all the iterated data, correspond
(`AlgebraicGeometry.Etale.frobeniusOperator_iterateWeilDatum_contragredientWeilDatum_unit`).

The comparison is carried out through the evaluation `Λ_X ⊗ᴸ Λ_X^∨ ⟶ Λ_X`, which characterises
both the identification `Λ_X^∨ ≅ Λ_X`
(`AlgebraicGeometry.Etale.coefficientDualUnitIso_hom`) and the contragredient datum
(`AlgebraicGeometry.Etale.derivedTensor_map_contragredientWeilDatum_comp_coefficientEvaluation`),
together with the left unitality of the tensor comparison of `Lg^*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.Adjunction

/-- If `G` is right adjoint to the identity, the comparison `G ≅ 𝟭` given by the uniqueness of
right adjoints is the counit. -/
lemma rightAdjointUniq_id_hom_app {C : Type*} [Category* C] {G : C ⥤ C} (adj : 𝟭 C ⊣ G)
    (X : C) : (adj.rightAdjointUniq Adjunction.id).hom.app X = adj.counit.app X := by
  simpa only [Functor.id_obj, Functor.id_map, Adjunction.id_counit, NatTrans.id_app,
    Functor.comp_obj, Category.comp_id] using rightAdjointUniq_hom_app_counit adj Adjunction.id X

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Etale

open Scheme

section General

variable {X : Scheme.{u}} (A : Type*) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

variable (X) in
/-- The identification `Λ_X^∨ ≅ Λ_X` obtained from the uniqueness of right adjoints of
`Λ_X ⊗ᴸ - ≅ 𝟭` is the evaluation `Λ_X^∨ ≅ Λ_X ⊗ᴸ Λ_X^∨ ⟶ Λ_X`. -/
lemma rightAdjointUniq_derivedTensorHomAdjunction_unit_hom_app :
    (((derivedTensorHomAdjunction A (𝟙_ _)).ofNatIsoLeft
      (derivedTensorLeftUnitorNatIso A X)).rightAdjointUniq Adjunction.id).hom.app (𝟙_ _) =
      (λ_ _).inv ≫ DerivedCategory.coefficientEvaluation (𝟙_ _) :=
  Adjunction.rightAdjointUniq_id_hom_app _ _

/-- An identification `e : Λ_X^∨ ≅ Λ_X` given by the evaluation `Λ_X^∨ ≅ Λ_X ⊗ᴸ Λ_X^∨ ⟶ Λ_X`
intertwines the contragredient datum of the canonical datum `ε : Lg^* Λ_X ≅ Λ_X` with `ε`. -/
lemma map_hom_comp_leftDerivedUpperStarUnitIso_hom [UpperStarPreservesFlat A] (g : X ⟶ X)
    (e : (DerivedCategory.coefficientDual A X).obj (op (𝟙_ _)) ≅ 𝟙_ _)
    (he : e.hom = (λ_ _).inv ≫ DerivedCategory.coefficientEvaluation (𝟙_ _)) :
    L((g)^*[A]).map e.hom ≫ (leftDerivedUpperStarUnitIso A g).hom =
      contragredientWeilDatum A g (leftDerivedUpperStarUnitIso A g) ≫ e.hom := by
  have h : 𝟙_ _ ◁ contragredientWeilDatum A g (leftDerivedUpperStarUnitIso A g) ≫
      DerivedCategory.coefficientEvaluation (𝟙_ _) =
      (leftDerivedUpperStarUnitIso A g).inv ▷ _ ≫
        (leftDerivedUpperStarTensorIso A g (𝟙_ _) _).inv ≫
          L((g)^*[A]).map (DerivedCategory.coefficientEvaluation (𝟙_ _)) ≫
            (leftDerivedUpperStarUnitIso A g).hom :=
    derivedTensor_map_contragredientWeilDatum_comp_coefficientEvaluation A g _
  have hl : L((g)^*[A]).map (λ_ ((DerivedCategory.coefficientDual A X).obj (op (𝟙_ _)))).inv =
      (λ_ _).inv ≫ (leftDerivedUpperStarUnitIso A g).inv ▷ _ ≫
        (leftDerivedUpperStarTensorIso A g (𝟙_ _) _).inv := by
    rw [← leftDerivedUpperStarTensorComparison_leftUnitor_inv A g, Category.assoc,
      Category.assoc, hom_inv_whiskerRight_assoc, ← leftDerivedUpperStarTensorIso_hom,
      Iso.hom_inv_id, Category.comp_id]
  rw [he, Functor.map_comp, Category.assoc, leftUnitor_inv_naturality_assoc, h, hl,
    Category.assoc, Category.assoc]

end General

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

variable (Λ X) in
/-- The identification `Λ_X^∨ ≅ Λ_X` is the evaluation `Λ_X^∨ ≅ Λ_X ⊗ᴸ Λ_X^∨ ⟶ Λ_X`. -/
lemma coefficientDualUnitIso_hom :
    (coefficientDualUnitIso Λ X).hom =
      (λ_ _).inv ≫ DerivedCategory.coefficientEvaluation (𝟙_ (DerivedCategoryModule Λ X)) :=
  rightAdjointUniq_derivedTensorHomAdjunction_unit_hom_app X (ModuleCat.{u + 1} Λ)

/-- Blueprint `theorem-poincare-duality-frobenius--1`: for `K = Λ_X` with its canonical datum
`ε : Lg^* Λ_X ≅ Λ_X`, the contragredient datum on `Λ_X^∨` corresponds to the canonical datum
under the canonical identification `e : Λ_X^∨ ≅ Λ_X`
(`AlgebraicGeometry.Etale.coefficientDualUnitIso`): `e` is a morphism of Weil objects
`(Λ_X^∨, φ_{Λ^∨}) ⟶ (Λ_X, ε)`, i.e. `ε ∘ Lg^* e = e ∘ φ_{Λ^∨}`. Here `g` is any endomorphism
of `X`. -/
theorem isWeilMorphism_coefficientDualUnitIso_hom (g : X ⟶ X) :
    IsWeilMorphism g (contragredientWeilDatum _ g (leftDerivedUpperStarUnitIso _ g))
      (leftDerivedUpperStarUnitIso _ g).hom (coefficientDualUnitIso Λ X).hom :=
  map_hom_comp_leftDerivedUpperStarUnitIso_hom (ModuleCat.{u + 1} Λ) g
    (coefficientDualUnitIso Λ X) (coefficientDualUnitIso_hom Λ X)

/-- Blueprint `theorem-poincare-duality-frobenius--1`: the identification `e : Λ_X^∨ ≅ Λ_X`
intertwines the contragredient datum of the canonical datum with the canonical datum,
`Lg^* e ≫ ε = φ_{Λ^∨} ≫ e` (`AlgebraicGeometry.Etale.isWeilMorphism_coefficientDualUnitIso_hom` in
explicit form). -/
theorem map_coefficientDualUnitIso_hom_comp_leftDerivedUpperStarUnitIso_hom (g : X ⟶ X) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map (coefficientDualUnitIso Λ X).hom ≫
        (leftDerivedUpperStarUnitIso _ g).hom =
      contragredientWeilDatum _ g (leftDerivedUpperStarUnitIso _ g) ≫
        (coefficientDualUnitIso Λ X).hom :=
  isWeilMorphism_coefficientDualUnitIso_hom g

section Iterate

variable {g : X ⟶ X} {M N : DerivedCategoryModule Λ X}
  {ψM : (L((g)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M}
  {ψN : (L((g)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N}

/-- A morphism of Weil objects for `g` is a morphism of Weil objects for every iterate `g^m`,
with the iterated data `ψ^{[m]}` (`AlgebraicGeometry.Etale.iterateWeilDatum`). -/
lemma IsWeilMorphism.iterateWeilDatum {f : M ⟶ N} (hf : IsWeilMorphism g ψM ψN f) (m : ℕ) :
    IsWeilMorphism (endIterate g m) (Etale.iterateWeilDatum Λ g ψM m)
      (Etale.iterateWeilDatum Λ g ψN m) f := by
  induction m with
  | zero => exact (leftDerivedUpperStarId _ X).hom.naturality f
  | succ m ih =>
    unfold IsWeilMorphism at hf ih ⊢
    rw [Etale.iterateWeilDatum, Etale.iterateWeilDatum, Category.assoc, Category.assoc,
      ← hf, ← Functor.map_comp_assoc, ← ih, Functor.map_comp_assoc]
    exact (leftDerivedUpperStarComp _ g (endIterate g m)).hom.naturality_assoc f _

end Iterate

/-- Blueprint `theorem-poincare-duality-frobenius--1`: the Frobenius operators of `(Λ_X^∨, φ_{Λ^∨})`
are those of `(Λ_X, ε)`, read through the identification `Λ_X^∨ ≅ Λ_X`. -/
theorem frobeniusOperator_contragredientWeilDatum_unit (g : X ⟶ X)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op (𝟙_ (DerivedCategoryModule Λ X)))) :
    frobeniusOperator g (contragredientWeilDatum _ g (leftDerivedUpperStarUnitIso _ g)) x ≫
        (coefficientDualUnitIso Λ X).hom =
      frobeniusOperator g (leftDerivedUpperStarUnitIso _ g).hom
        (x ≫ (coefficientDualUnitIso Λ X).hom) :=
  ((isWeilMorphism_coefficientDualUnitIso_hom g).frobeniusOperator_comp x).symm

/-- Blueprint `theorem-poincare-duality-frobenius--1`: the Frobenius operators of the iterates
`φ_{Λ^∨}^{[m]}` of the contragredient datum on `Λ_X^∨` are the iterated global geometric
Frobenius operators, those of the iterates `ε^{[m]}` of the canonical datum on `Λ_X`, read through
the identification `Λ_X^∨ ≅ Λ_X`. -/
theorem frobeniusOperator_iterateWeilDatum_contragredientWeilDatum_unit (g : X ⟶ X) (m : ℕ)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op (𝟙_ (DerivedCategoryModule Λ X)))) :
    frobeniusOperator (endIterate g m)
        (iterateWeilDatum Λ g (contragredientWeilDatum _ g (leftDerivedUpperStarUnitIso _ g)) m)
          x ≫ (coefficientDualUnitIso Λ X).hom =
      frobeniusOperator (endIterate g m)
        (iterateWeilDatum Λ g (leftDerivedUpperStarUnitIso _ g).hom m)
        (x ≫ (coefficientDualUnitIso Λ X).hom) :=
  (((isWeilMorphism_coefficientDualUnitIso_hom g).iterateWeilDatum m).frobeniusOperator_comp
    x).symm

end AlgebraicGeometry.Etale
