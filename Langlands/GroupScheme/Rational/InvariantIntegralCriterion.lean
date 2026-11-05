import Langlands.GroupScheme.Lie.ConjugationDerivation
import Langlands.GroupScheme.Rational.InvariantCoordinateIntegral

/-! # A universal-coordinate criterion for invariant integration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateIntegration

variable {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]

/-- Every actual affine point is obtained from the coordinate point. -/
theorem affineMap_coordinatePoint {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) :
    Lie.affineMap H (Lie.pointCoordinates H t) (Lie.universalPoint H) = t := by
  rw [Lie.affineMap_universalPoint]
  exact (Lie.pointCoordinates H).symm_apply_apply t

/-- Actual multiplication induces the coordinate coproduct. -/
def coordinateCoproduct : Coord H →ₐ[k] Coord H ⊗[k] Coord H :=
  ((leftTranslation H (Coord H) (Lie.universalPoint H)).restrictScalars k).comp
    Algebra.TensorProduct.includeRight

/-- Scalar extension of the coefficient algebra commutes with translation. -/
theorem tensorMap_leftTranslation {A B : Type u}
    [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (t : Lie.AffinePoints H A) :
    (tensorMap H f).comp ((leftTranslation H A t).restrictScalars k) =
      ((leftTranslation H B (Lie.affineMap H f t)).restrictScalars k).comp
        (tensorMap H f) := by
  apply Algebra.TensorProduct.ext
  · ext a
    change tensorMap H f
        (leftTranslation H A t ((algebraMap A (A ⊗[k] Coord H)) a)) =
      leftTranslation H B (Lie.affineMap H f t)
        ((algebraMap B (B ⊗[k] Coord H)) (f a))
    rw [(leftTranslation H A t).commutes,
      (leftTranslation H B (Lie.affineMap H f t)).commutes]
    rfl
  · have hp :
        Lie.affineMap H (tensorMap H f)
            (Lie.affineMap H ((leftTranslation H A t).restrictScalars k)
              (universalPoint H A)) =
          Lie.affineMap H ((leftTranslation H B (Lie.affineMap H f t)).restrictScalars k)
            (Lie.affineMap H (tensorMap H f) (universalPoint H A)) := by
      rw [leftTranslation_universalPoint, map_mul, tensorMap_universalPoint,
        leftTranslation_universalPoint]
      congr 1
      rw [← Lie.affineMap_comp, tensorMap_includeLeft, Lie.affineMap_comp]
    have hc := congrArg (Lie.pointCoordinates H) hp
    rw [Lie.pointCoordinates_naturality, Lie.pointCoordinates_naturality,
      Lie.pointCoordinates_naturality, Lie.pointCoordinates_naturality] at hc
    simp only [universalPoint, Equiv.apply_symm_apply] at hc
    ext z
    exact AlgHom.congr_fun hc z

/-- Translation of a coordinate function is obtained from the coproduct by
specializing its first factor to the supplied actual point. -/
theorem leftTranslation_includeRight {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) (z : Coord H) :
    leftTranslation H A t (Algebra.TensorProduct.includeRight z) =
      tensorMap H (Lie.pointCoordinates H t) (coordinateCoproduct H z) := by
  have h := AlgHom.congr_fun
    (tensorMap_leftTranslation H (Lie.pointCoordinates H t) (Lie.universalPoint H))
    (Algebra.TensorProduct.includeRight z)
  rw [affineMap_coordinatePoint] at h
  simpa [coordinateCoproduct, Algebra.TensorProduct.includeRight_apply] using h.symm

/-- One coordinate-coproduct contraction identity implies invariance under
all actual translations over every coefficient algebra. -/
theorem left_invariant_of_coordinateCoproduct
    (ℓ : Coord H →ₗ[k] k)
    (hℓ : ∀ z : Coord H,
      contract H (Coord H) ℓ (coordinateCoproduct H z) =
        algebraMap k (Coord H) (ℓ z))
    (A : Type u) [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) (x : A ⊗[k] Coord H) :
    contract H A ℓ (leftTranslation H A t x) = contract H A ℓ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
    have hz : contract H A ℓ
        (leftTranslation H A t (Algebra.TensorProduct.includeRight z)) =
        algebraMap k A (ℓ z) := by
      rw [leftTranslation_includeRight, contract_naturality, hℓ,
        (Lie.pointCoordinates H t).commutes]
    have hx : a ⊗ₜ[k] z = a •
        (Algebra.TensorProduct.includeRight z : A ⊗[k] Coord H) := by
      rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
    rw [hx, map_smul, map_smul, hz, map_smul]
    simp [Algebra.TensorProduct.includeRight_apply, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The coproduct identity is equivalent to the full all-algebra translation
law, without a normalization assumption. -/
theorem left_invariant_iff_coordinateCoproduct (ℓ : Coord H →ₗ[k] k) :
    (∀ (A : Type u) [CommRing A] [Algebra k A]
      (t : Lie.AffinePoints H A) (x : A ⊗[k] Coord H),
      contract H A ℓ (leftTranslation H A t x) = contract H A ℓ x) ↔
    ∀ z : Coord H,
      contract H (Coord H) ℓ (coordinateCoproduct H z) =
        algebraMap k (Coord H) (ℓ z) := by
  constructor
  · intro h z
    simpa [coordinateCoproduct, Algebra.TensorProduct.includeRight_apply] using
      h (Coord H) (Lie.universalPoint H) (Algebra.TensorProduct.includeRight z)
  · exact left_invariant_of_coordinateCoproduct H ℓ

/-- Construct the full invariant-integral interface from normalization and
one actual coordinate-coproduct identity. -/
def InvariantIntegral.ofCoordinateCoproduct (ℓ : Coord H →ₗ[k] k)
    (h1 : ℓ 1 = 1)
    (hℓ : ∀ z : Coord H,
      contract H (Coord H) ℓ (coordinateCoproduct H z) =
        algebraMap k (Coord H) (ℓ z)) : InvariantIntegral H where
  linearForm := ℓ
  map_one := h1
  left_invariant := left_invariant_of_coordinateCoproduct H ℓ hℓ

end Langlands.GroupScheme.CoordinateIntegration
