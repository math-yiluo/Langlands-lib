import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.LinearActionBaseChange
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Restriction of invertible projective coordinate changes -/

noncomputable section

open CategoryTheory AlgebraicGeometry Matrix

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

variable {K R A : Type u} [CommRing K] [CommRing R] [CommRing A] (n : ℕ)

/-- Map every coefficient of an invertible coordinate matrix by a ring homomorphism. -/
def coordinateBaseChange (φ : K →+* R) :
    ((Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) →*
      ((Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :=
  (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv R _)).toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.map φ).comp
      (Matrix.GeneralLinearGroup.toLin.trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv K _)).symm.toMonoidHom)

@[simp]
lemma coordinateBaseChange_coeff (φ : K →+* R)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) (i j : Fin (n + 1)) :
    coordinateBaseChange n φ e (Pi.single j 1) i = φ (e (Pi.single j 1) i) := by
  change ((Matrix.GeneralLinearGroup.map φ
    (Matrix.GeneralLinearGroup.toLin.symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv e)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ Pi.single j 1) i = _
  rw [Matrix.mulVec_single_one]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equality on all coordinate basis vectors determines a coordinate equivalence. -/
lemma coordinateEquiv_ext
    {e f : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)}
    (h : ∀ i j, e (Pi.single j 1) i = f (Pi.single j 1) i) : e = f := by
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin (n + 1))).ext
  intro j
  ext i
  rw [Pi.basisFun_apply]
  exact h i j

@[simp]
lemma coordinateBaseChange_id
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    coordinateBaseChange n (RingHom.id K) e = e := by
  apply coordinateEquiv_ext n
  intro i j
  simp

@[simp]
lemma coordinateBaseChange_comp (φ : K →+* R) (ψ : R →+* A)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    coordinateBaseChange n (ψ.comp φ) e =
      coordinateBaseChange n ψ (coordinateBaseChange n φ e) := by
  apply coordinateEquiv_ext n
  intro i j
  simp

@[simp]
lemma coordinateBaseChange_refl (φ : K →+* R) :
    coordinateBaseChange n φ (LinearEquiv.refl K _) = LinearEquiv.refl R _ :=
  map_one (coordinateBaseChange n φ)

lemma coordinateBaseChange_trans (φ : K →+* R)
    (e f : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    coordinateBaseChange n φ (e.trans f) =
      (coordinateBaseChange n φ e).trans (coordinateBaseChange n φ f) :=
  map_mul (coordinateBaseChange n φ) f e

@[simp]
lemma coordinateBaseChange_symm (φ : K →+* R)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    coordinateBaseChange n φ e.symm = (coordinateBaseChange n φ e).symm :=
  map_inv (coordinateBaseChange n φ) e

@[reassoc]
lemma coefficientMap_linearAction_baseChange (φ : K →+* R)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    coefficientMap n φ ≫ linearAction K n e =
      linearAction R n (coordinateBaseChange n φ e) ≫ coefficientMap n φ := by
  apply coefficientMap_linearAction
  intro i j
  exact (coordinateBaseChange_coeff n φ e i j).symm

end Langlands.AlgebraicGeometry.ProjectiveSpace

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

variable {K R : Type u} [CommRing K] [CommRing R]
  {S T : Scheme.{u}} {n : ℕ}

/-- An actual relative coordinate change is unchanged after extending its matrix coefficients. -/
lemma linearAction_baseChange (a : S ⟶ Spec (CommRingCat.of K))
    (b : S ⟶ Spec (CommRingCat.of R)) (φ : K →+* R)
    (w : b ≫ Spec.map (CommRingCat.ofHom φ) = a)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    linearAction a e = linearAction b (ProjectiveSpace.coordinateBaseChange n φ e) := by
  apply linearAction_coefficientMap a b φ w
  intro i j
  exact (ProjectiveSpace.coordinateBaseChange_coeff n φ e i j).symm

/-- Simultaneous scheme and coefficient restriction for the constructed coordinate change. -/
@[reassoc]
lemma map_linearAction_baseChange (a : S ⟶ Spec (CommRingCat.of K))
    (b : T ⟶ Spec (CommRingCat.of R)) (f : T ⟶ S) (φ : K →+* R)
    (w : b ≫ Spec.map (CommRingCat.ofHom φ) = f ≫ a)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) :
    map n f ≫ linearAction a e =
      linearAction b (ProjectiveSpace.coordinateBaseChange n φ e) ≫ map n f := by
  apply map_linearAction_coefficientMap a b f φ w
  intro i j
  exact (ProjectiveSpace.coordinateBaseChange_coeff n φ e i j).symm

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
