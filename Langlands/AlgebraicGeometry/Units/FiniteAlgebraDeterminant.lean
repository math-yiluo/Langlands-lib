import Langlands.AlgebraicGeometry.Units.RelativeGlobalUnits
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.MvPolynomial.Basic

/-! # Determinant-open candidates for finite algebra units -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.FiniteAlgebraUnits

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- The ground-field spectrum. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} := Spec (CommRingCat.of k)

/-- The actual finite-algebra scheme over the field. -/
abbrev algebraSchemeMap (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    Spec (CommRingCat.of A) ⟶ base k :=
  Spec.map (CommRingCat.ofHom (algebraMap k A))

/-- The actual global-unit presheaf on all schemes over the field. -/
abbrev presheaf (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    AlgebraicSpace.Presheaf (base k) :=
  RelativeGlobalUnits.presheaf (algebraSchemeMap k A)

/-- Coordinate ring of the affine space attached to a finite basis. -/
abbrev coordinateRing (k : Type u) [Field k] (n : ℕ) := MvPolynomial (Fin n) k

variable {n : ℕ} (b : Module.Basis (Fin n) k A)

/-- The generic element, with polynomial coordinates in the first tensor factor. -/
def genericElement : coordinateRing k n ⊗[k] A :=
  ∑ i, MvPolynomial.X i ⊗ₜ[k] b i

/-- The determinant of multiplication by the generic element. -/
def determinant : coordinateRing k n :=
  Algebra.norm (coordinateRing k n) (genericElement b)

lemma determinant_eq_det :
    determinant b =
      LinearMap.det (Algebra.lmul (coordinateRing k n)
        (coordinateRing k n ⊗[k] A) (genericElement b)) := rfl

lemma determinant_eq_matrix_det :
    determinant b =
      (Algebra.leftMulMatrix (b.baseChange (coordinateRing k n)) (genericElement b)).det :=
  Algebra.norm_eq_matrix_det _ _

/-- The away-localization whose spectrum is the determinant-open candidate. -/
abbrev candidateRing := Localization.Away (determinant b)

/-- The concrete candidate as a scheme over the field. -/
def candidate : Over (base k) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (candidateRing b))))

/-- The generic element after passing to the determinant-open coordinate ring. -/
def localizedGenericElement : candidateRing b ⊗[k] A :=
  Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom k (coordinateRing k n) (candidateRing b))
    (AlgHom.id k A) (genericElement b)

lemma localizedGenericElement_eq_sum :
    localizedGenericElement b =
      ∑ i, algebraMap (coordinateRing k n) (candidateRing b) (MvPolynomial.X i) ⊗ₜ[k] b i := by
  simp [localizedGenericElement, genericElement]

section ChangeCoefficients

variable {R C : Type u} [CommRing R] [CommRing C] [Algebra k R] [Algebra k C]
  (φ : R →ₐ[k] C)

/-- Multiplication matrices commute with a change in the coefficient tensor factor. -/
lemma leftMulMatrix_map (x : R ⊗[k] A) :
    Algebra.leftMulMatrix (b.baseChange C)
        (Algebra.TensorProduct.map φ (AlgHom.id k A) x) =
      (Algebra.leftMulMatrix (b.baseChange R) x).map φ := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    ext i j
    simp [Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.smul_def]
  | add x y hx hy => simp [map_add, hx, hy, Matrix.map_add]

include b in
/-- The finite-free norm commutes with this coefficient change, without any
nontriviality assumption on the algebra. -/
lemma norm_map (x : R ⊗[k] A) :
    Algebra.norm C (Algebra.TensorProduct.map φ (AlgHom.id k A) x) =
      φ (Algebra.norm R x) := by
  rw [Algebra.norm_eq_matrix_det (b.baseChange C),
    leftMulMatrix_map b φ, Algebra.norm_eq_matrix_det (b.baseChange R)]
  exact (φ.map_det _).symm

end ChangeCoefficients

/-- The localized generic element is invertible, including for the zero algebra. -/
lemma localizedGenericElement_isUnit : IsUnit (localizedGenericElement b) := by
  let : Module.Free (candidateRing b) (candidateRing b ⊗[k] A) :=
    Module.Free.of_basis (b.baseChange (candidateRing b))
  let : Module.Finite (candidateRing b) (candidateRing b ⊗[k] A) :=
    Module.Finite.of_basis (b.baseChange (candidateRing b))
  apply (Algebra.lmul_isUnit_iff (R := candidateRing b)).mp
  apply (LinearMap.isUnit_iff_isUnit_det _).mpr
  change IsUnit (Algebra.norm (candidateRing b) (localizedGenericElement b))
  rw [localizedGenericElement, norm_map b]
  exact IsLocalization.Away.algebraMap_isUnit (determinant b)

/-- A unit with the localized generic element as its underlying value. -/
def algebraicUniversalUnit : (candidateRing b ⊗[k] A)ˣ :=
  (localizedGenericElement_isUnit b).unit

@[simp]
lemma algebraicUniversalUnit_val :
    (algebraicUniversalUnit b : candidateRing b ⊗[k] A) = localizedGenericElement b :=
  (localizedGenericElement_isUnit b).unit_spec

/-- In rank zero the determinant is the determinant of the empty matrix, namely one. -/
lemma determinant_rank_zero (b₀ : Module.Basis (Fin 0) k A) :
    determinant b₀ = 1 := by
  rw [determinant_eq_matrix_det]
  exact Matrix.det_isEmpty

end Langlands.AlgebraicGeometry.FiniteAlgebraUnits
