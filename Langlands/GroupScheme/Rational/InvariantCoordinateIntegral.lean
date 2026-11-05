import Langlands.GroupScheme.Lie.AffineCoordinates
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Normalized invariant integration on actual affine group coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CoordinateIntegration

variable {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]

/-- The coordinate algebra of the supplied affine group. -/
abbrev Coord := Lie.coordinateAlgebra H

variable (A : Type u) [CommRing A] [Algebra k A]

/-- The universal group point in the second factor of the tensor algebra. -/
def universalPoint : Lie.AffinePoints H (A ⊗[k] Coord H) :=
  (Lie.pointCoordinates H).symm Algebra.TensorProduct.includeRight

/-- Pullback of left translation by an actual point, fixing the coefficient
algebra. -/
def leftTranslation (t : Lie.AffinePoints H A) :
    A ⊗[k] Coord H →ₐ[A] A ⊗[k] Coord H :=
  AlgHom.liftEquiv k A (Coord H) (A ⊗[k] Coord H)
    (Lie.pointCoordinates H
      (Lie.affineMap H Algebra.TensorProduct.includeLeft t * universalPoint H A))

variable {A}

@[simp]
theorem leftTranslation_includeLeft (t : Lie.AffinePoints H A) :
    ((leftTranslation H A t).restrictScalars k).comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord H) =
        Algebra.TensorProduct.includeLeft := by
  ext a
  exact (leftTranslation H A t).commutes a

/-- Translation carries the universal point to its actual left translate. -/
theorem leftTranslation_universalPoint (t : Lie.AffinePoints H A) :
    Lie.affineMap H ((leftTranslation H A t).restrictScalars k)
      (universalPoint H A) =
        Lie.affineMap H Algebra.TensorProduct.includeLeft t * universalPoint H A := by
  apply (Lie.pointCoordinates H).injective
  rw [Lie.pointCoordinates_naturality, universalPoint, Equiv.apply_symm_apply]
  exact (AlgHom.liftEquiv k A (Coord H) (A ⊗[k] Coord H)).symm_apply_apply _

/-- Translation fixes every point pulled up from the coefficient algebra. -/
theorem leftTranslation_constant {G : GroupScheme (Spec (CommRingCat.of k))}
    (t : Lie.AffinePoints H A) (g : Lie.AffinePoints G A) :
    Lie.affineMap G ((leftTranslation H A t).restrictScalars k)
      (Lie.affineMap G Algebra.TensorProduct.includeLeft g) =
        Lie.affineMap G Algebra.TensorProduct.includeLeft g := by
  rw [← Lie.affineMap_comp, leftTranslation_includeLeft]

/-- Extend a map of coefficient algebras while fixing the coordinate factor. -/
def tensorMap {B : Type u} [CommRing B] [Algebra k B] (f : A →ₐ[k] B) :
    A ⊗[k] Coord H →ₐ[k] B ⊗[k] Coord H :=
  Algebra.TensorProduct.map f (AlgHom.id k (Coord H))

@[simp]
theorem tensorMap_tmul {B : Type u} [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (a : A) (z : Coord H) :
    tensorMap H f (a ⊗ₜ[k] z) = f a ⊗ₜ[k] z :=
  rfl

@[simp]
theorem tensorMap_includeLeft {B : Type u} [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) :
    (tensorMap H f).comp Algebra.TensorProduct.includeLeft =
      Algebra.TensorProduct.includeLeft.comp f := by
  ext a
  simp [Algebra.TensorProduct.includeLeft_apply]

/-- The universal point is preserved by maps of coefficient algebras. -/
theorem tensorMap_universalPoint {B : Type u} [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) :
    Lie.affineMap H (tensorMap H f) (universalPoint H A) =
      universalPoint H B := by
  apply (Lie.pointCoordinates H).injective
  rw [Lie.pointCoordinates_naturality, universalPoint, universalPoint,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext z
  simp [Algebra.TensorProduct.includeRight_apply]

variable (A)

/-- Extend a linear functional on the coordinate algebra to an A-linear
contraction of its coordinate factor. -/
def contract (ℓ : Coord H →ₗ[k] k) : A ⊗[k] Coord H →ₗ[A] A :=
  (TensorProduct.AlgebraTensorModule.rid k A A).toLinearMap ∘ₗ ℓ.baseChange A

@[simp]
theorem contract_tmul (ℓ : Coord H →ₗ[k] k) (a : A) (z : Coord H) :
    contract H A ℓ (a ⊗ₜ[k] z) = algebraMap k A (ℓ z) * a := by
  change (ℓ z) • a = _
  rw [Algebra.smul_def]

variable {A}

/-- Contraction is natural in every original coefficient algebra. -/
theorem contract_naturality {B : Type u} [CommRing B] [Algebra k B]
    (ℓ : Coord H →ₗ[k] k) (f : A →ₐ[k] B) (x : A ⊗[k] Coord H) :
    contract H B ℓ (tensorMap H f x) = f (contract H A ℓ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a z => simp only [tensorMap_tmul, contract_tmul, map_mul, f.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A normalized linear functional invariant under all actual left translations
after arbitrary extension of the coefficient algebra. -/
structure InvariantIntegral where
  linearForm : Coord H →ₗ[k] k
  map_one : linearForm 1 = 1
  left_invariant : ∀ (A : Type u) [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints H A) (x : A ⊗[k] Coord H),
    contract H A linearForm (leftTranslation H A t x) = contract H A linearForm x

namespace InvariantIntegral

variable {H} (I : InvariantIntegral H)

/-- Integrate the coordinate factor with the normalized invariant functional. -/
abbrev average : A ⊗[k] Coord H →ₗ[A] A :=
  contract H A I.linearForm

@[simp]
theorem average_includeLeft (a : A) :
    I.average ((Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] Coord H) a) = a := by
  simp [average, Algebra.TensorProduct.includeLeft_apply, I.map_one]

end InvariantIntegral

end Langlands.GroupScheme.CoordinateIntegration
