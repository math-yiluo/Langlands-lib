/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData

import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback

/-! # The geometric input to analytic integral matrix charts -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem pulled_matrix_entry (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) {n t : ℕ}
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (i : Fin t) (j : Fin n) :
    biproduct.ι (fun _ : Fin n ↦ Mod.regular
      (condensedRingObj (integralCoeff ℓ E) Y)) j ≫
        integralMatrixPullbackMap ℓ E f a ≫
          biproduct.π (fun _ : Fin t ↦ Mod.regular
            (condensedRingObj (integralCoeff ℓ E) Y)) i =
      (integralRegularPullbackIso ℓ E f).inv ≫
        (integralMatrixPullback ℓ E f).map
          (biproduct.ι (fun _ : Fin n ↦ Mod.regular
            (condensedRingObj (integralCoeff ℓ E) X)) j ≫ a ≫
              biproduct.π (fun _ : Fin t ↦ Mod.regular
                (condensedRingObj (integralCoeff ℓ E) X)) i) ≫
            (integralRegularPullbackIso ℓ E f).hom := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let T := integralMatrixPullback ℓ E f
  let e := integralRegularPullbackIso ℓ E f
  have he (r : ℕ) : integralFiniteFreePullbackIso ℓ E f r =
      T.mapBiproduct (fun _ : Fin r ↦ Mod.regular R) ≪≫
        biproduct.mapIso (fun _ ↦ e) := by
    unfold integralFiniteFreePullbackIso
    unfold e integralRegularPullbackIso
    rfl
  have hπ : (biproduct.lift fun j : Fin t ↦
      T.map (biproduct.π (fun _ : Fin t ↦ Mod.regular R) j)) ≫
        biproduct.π (T.obj ∘ (fun _ : Fin t ↦ Mod.regular R)) i =
          T.map (biproduct.π (fun _ : Fin t ↦ Mod.regular R) i) :=
    biproduct.lift_π _ _
  simp only [integralMatrixPullbackMap, he, Iso.trans_inv, Iso.trans_hom,
    biproduct.mapIso_inv, biproduct.mapIso_hom, Category.assoc,
    biproduct.ι_map_assoc, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc,
    biproduct.map_π, Functor.mapBiproduct_hom,
    Functor.map_comp]
  rw [reassoc_of% hπ]

theorem matrix_coefficient_pullback (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) {n t : ℕ}
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (i : Fin t) (j : Fin n) (y : Y) :
    integralMatrixPullbackFunctions ℓ E f a i j y =
      integralMatrixFunctions ℓ E X
        (chartComparison X (continuousIntegers ℓ E)) a i j (f y) := by
  unfold integralMatrixPullbackFunctions
  change integralRegularCoefficient ℓ E Y
    (biproduct.ι (fun _ : Fin n ↦ Mod.regular
      (condensedRingObj (integralCoeff ℓ E) Y)) j ≫
        integralMatrixPullbackMap ℓ E f a ≫
          biproduct.π (fun _ : Fin t ↦ Mod.regular
            (condensedRingObj (integralCoeff ℓ E) Y)) i) y =
      integralRegularCoefficient ℓ E X
        (biproduct.ι (fun _ : Fin n ↦ Mod.regular
          (condensedRingObj (integralCoeff ℓ E) X)) j ≫ a ≫
            biproduct.π (fun _ : Fin t ↦ Mod.regular
              (condensedRingObj (integralCoeff ℓ E) X)) i) (f y)
  rw [pulled_matrix_entry]
  exact integralRegularCoefficient_pullback ℓ E f _ y

/-- Canonical continuous matrix coefficients commute with a second pullback.

Source: Bhatt--Scholze, Section 6.8, continuous coefficient realization;
functoriality of the specified inverse image and its finite biproduct comparison.
(auxiliary; not a blueprint node)

Proof: express each matrix entry as inclusion, the matrix morphism, then projection.
Naturality of the biproduct comparison commutes these inclusions and projections
with pullback. The regular-module comparison identifies the remaining entry with
the pullback of the original regular endomorphism. Conjugate by the canonical
continuous coefficient realization. The adjunction defining chartComparison is
natural in the scheme: on every profinite test object both composites first apply
the test projection and then the same continuous coefficient function. Consequently
the conjugated regular endomorphism multiplies by the composite of the original
coefficient function with the underlying scheme map. Evaluate at the unit section.
The inverse-image composition comparison and coefficient pullback comparison cancel
to identify this iterated pullback with the canonical pullback along g≫f.
This proves the asserted pointwise equality for every row and column, including
empty schemes and empty matrices. -/
theorem integralMatrixFunctions_pullback (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) {n t : ℕ}
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (i : Fin t) (j : Fin n) (z : Z) :
    integralMatrixPullbackFunctions ℓ E (g ≫ f) a i j z =
      integralMatrixPullbackFunctions ℓ E f a i j (g z) := by
  rw [matrix_coefficient_pullback, matrix_coefficient_pullback]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
