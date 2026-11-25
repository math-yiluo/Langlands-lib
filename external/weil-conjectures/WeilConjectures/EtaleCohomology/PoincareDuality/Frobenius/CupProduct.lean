/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# The cup product is Frobenius equivariant

For an endomorphism `g : X ⟶ X`, the Frobenius operators `x ↦ ε⁻¹ ≫ Lg^* x ≫ ε[n]` of the
canonical Weil datum `ε : Lg^* Λ_X ≅ Λ_X` on the cohomology classes `Λ_X ⟶ Λ_X[n]` are
multiplicative for the cup product
(`AlgebraicGeometry.Etale.frobeniusOperator_cupProduct`): the cup product is the Yoneda product
(`CategoryTheory.MonoidalCategory.shiftProduct_eq`), and `Lg^*` commutes with the shifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} (g : X ⟶ X)

/-- The Frobenius operator of a shifted datum on a Yoneda product: for `x : Λ_X ⟶ Λ_X[i]` and
`z : Λ_X ⟶ M`, `F(x ≫ z[i]) = F(x) ≫ F(z)[i]`. -/
lemma frobeniusOperator_comp_shift {M : DerivedCategoryModule Λ X}
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) (i : ℤ)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦i⟧)
    (z : 𝟙_ (DerivedCategoryModule Λ X) ⟶ M) :
    frobeniusOperator g (shiftWeilDatum g ψ i) (x ≫ z⟦i⟧') =
      frobeniusOperator g (shiftWeilDatum g (leftDerivedUpperStarUnitIso _ g).hom i) x ≫
        (frobeniusOperator g ψ z)⟦i⟧' := by
  rw [frobeniusOperator_apply, frobeniusOperator_apply, frobeniusOperator_apply, shiftWeilDatum,
    shiftWeilDatum, Functor.map_comp, Category.assoc, Category.assoc,
    Functor.commShiftIso_hom_naturality_assoc]
  simp

/-- **The cup product is Frobenius equivariant**: `F(x ⌣ y) = F(x) ⌣ F(y)` for the Frobenius
operators of the canonical Weil datum of `Λ_X`. -/
theorem frobeniusOperator_cupProduct (i j : ℤ)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦j⟧) :
    frobeniusOperator g (shiftWeilDatum g (leftDerivedUpperStarUnitIso _ g).hom (i + j))
        (cupProduct _ i j x y) =
      cupProduct _ i j
        (frobeniusOperator g (shiftWeilDatum g (leftDerivedUpperStarUnitIso _ g).hom i) x)
        (frobeniusOperator g (shiftWeilDatum g (leftDerivedUpperStarUnitIso _ g).hom j) y) := by
  have h := DerivedCategory.unitorsCommShift (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  rw [cupProduct_eq_shiftProduct, cupProduct_eq_shiftProduct, shiftProduct_eq h,
    shiftProduct_eq h, ← cancel_mono ((shiftFunctorAdd' _ j i (i + j) (add_comm j i)).hom.app _),
    ← frobeniusOperator_shiftWeilDatum_comp_shiftFunctorAdd']
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id, Category.comp_id]
  exact frobeniusOperator_comp_shift g _ i x y

end AlgebraicGeometry.Etale
