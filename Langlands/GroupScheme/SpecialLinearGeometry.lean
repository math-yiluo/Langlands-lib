import Langlands.GroupScheme.SpecialLinear
import Langlands.GroupScheme.Reductive.GeneralLinear

/-! # A determinant retraction and geometry of the actual special linear group -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SpecialLinear

section Matrices

variable {n : Type v} [Fintype n] [DecidableEq n] (p : n)
variable {A : Type u} [CommRing A]

/-- The diagonal invertible matrix with the given unit in position `p`. -/
def pivotDiagonal (a : Aˣ) : GL n A where
  val := Matrix.diagonal fun i => if i = p then (a : A) else 1
  inv := Matrix.diagonal fun i => if i = p then (↑a⁻¹ : A) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    split_ifs <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    split_ifs <;> simp

@[simp] theorem det_pivotDiagonal (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (pivotDiagonal p a) = a := by
  apply Units.ext
  simp [pivotDiagonal, Matrix.GeneralLinearGroup.det]

@[simp] theorem pivotDiagonal_one : pivotDiagonal p (1 : Aˣ) = 1 := by
  apply Units.ext
  simp [pivotDiagonal]

variable {B : Type w} [CommRing B]

/-- The pivot matrix commutes with every coefficient homomorphism. -/
theorem map_pivotDiagonal (f : A →+* B) (a : Aˣ) :
    Matrix.GeneralLinearGroup.map f (pivotDiagonal p a) =
      pivotDiagonal p (Units.map f a) := by
  apply Units.ext
  ext i j
  simp [pivotDiagonal, Matrix.diagonal_apply]
  split_ifs <;> simp_all

/-- Normalize an invertible matrix by multiplying its pivot row by its inverse determinant. -/
def normalize (g : GL n A) : Matrix.SpecialLinearGroup n A :=
  ⟨(pivotDiagonal p (Matrix.GeneralLinearGroup.det g)⁻¹ * g : GL n A).val, by
    change (↑(Matrix.GeneralLinearGroup.det
      (pivotDiagonal p (Matrix.GeneralLinearGroup.det g)⁻¹ * g)) : A) = 1
    rw [map_mul, det_pivotDiagonal, inv_mul_cancel, Units.val_one]⟩

/-- The normalized matrix is the indicated product in the general linear group. -/
theorem toGL_normalize (g : GL n A) :
    Matrix.SpecialLinearGroup.toGL (normalize p g) =
      pivotDiagonal p (Matrix.GeneralLinearGroup.det g)⁻¹ * g := by
  apply Units.ext
  rfl

/-- Normalization is natural in the coefficient ring. -/
theorem normalize_map (f : A →+* B) (g : GL n A) :
    normalize p (Matrix.GeneralLinearGroup.map f g) =
      Matrix.SpecialLinearGroup.map f (normalize p g) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have ht : Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map f (normalize p g)) =
      Matrix.GeneralLinearGroup.map f (Matrix.SpecialLinearGroup.toGL (normalize p g)) :=
    Units.ext rfl
  rw [ht, toGL_normalize, toGL_normalize, map_mul, map_pivotDiagonal,
    Matrix.GeneralLinearGroup.map_det, map_inv]

/-- Normalization retracts the ordinary determinant-one inclusion. -/
@[simp] theorem normalize_toGL (g : Matrix.SpecialLinearGroup n A) :
    normalize p (Matrix.SpecialLinearGroup.toGL g) = g := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_normalize]
  have hd : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL g) = 1 := by
    apply Units.ext
    exact g.property
  rw [hd, inv_one, pivotDiagonal_one, one_mul]

end Matrices

section Coordinates

variable (n : Type) [Fintype n] [DecidableEq n] (p : n)
variable (R : Type u) [CommRing R]

/-- Restrict general-linear coordinate functions to determinant-one matrices. -/
def restrictCoordinates : GeneralLinear.CoordinateRing n R →ₐ[R] CoordinateRing n R :=
  GeneralLinear.classify (Matrix.SpecialLinearGroup.toGL (universal n R))

/-- Pull back special-linear coordinate functions along determinant normalization. -/
def normalizeCoordinates : CoordinateRing n R →ₐ[R] GeneralLinear.CoordinateRing n R :=
  classify (normalize p (GeneralLinear.universal n R))

/-- The two coordinate homomorphisms exhibit the special-linear ring as a retract. -/
theorem restrict_comp_normalize :
    (restrictCoordinates n R).comp (normalizeCoordinates n p R) =
      AlgHom.id R (CoordinateRing n R) := by
  apply homEquiv.injective
  change point _ = point _
  rw [point_comp]
  change Matrix.SpecialLinearGroup.map (restrictCoordinates n R).toRingHom
    (point (classify (normalize p (GeneralLinear.universal n R)))) = _
  rw [point_classify, ← normalize_map]
  change normalize p (GeneralLinear.point (restrictCoordinates n R)) = _
  rw [restrictCoordinates, GeneralLinear.point_classify, normalize_toGL, point_id]

/-- The actual determinant-one coordinate ring is finitely presented over its base. -/
instance finitePresentation_coordinateRing :
    Algebra.FinitePresentation R (CoordinateRing n R) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)

include p in
/-- The determinant-one coordinate ring is a smooth algebra over every base ring. -/
theorem coordinateRing_smooth : Algebra.Smooth R (CoordinateRing n R) := by
  let := GeneralLinear.coordinateRing_smooth n R
  let f := restrictCoordinates n R
  let j := normalizeCoordinates n p R
  have h : f.comp j = AlgHom.id R (CoordinateRing n R) := restrict_comp_normalize n p R
  have : Algebra.FormallySmooth R (CoordinateRing n R) :=
    Algebra.FormallySmooth.of_split f
      ((Ideal.Quotient.mkₐ R (RingHom.ker f.toRingHom ^ 2)).comp j) (by
        ext x
        change f.kerSquareLift (Ideal.Quotient.mk _ (j x)) = x
        rw [AlgHom.kerSquareLift_mk]
        exact AlgHom.congr_fun h x)
  exact ⟨inferInstance, inferInstance⟩

end Coordinates

section Schemes

variable (n : Type) [Fintype n] [DecidableEq n] (p : n)

include p in
/-- The structure morphism of the actual special-linear group is smooth. -/
theorem smooth_groupScheme (R : CommRingCat.{u}) :
    Smooth (groupScheme n R).X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing n R))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap R (CoordinateRing n R)).Smooth
  rw [RingHom.smooth_algebraMap]
  exact coordinateRing_smooth n p R

/-- The spectrum map induced by normalization is surjective. -/
theorem comap_normalizeCoordinates_surjective (R : Type u) [CommRing R] :
    Function.Surjective (PrimeSpectrum.comap (normalizeCoordinates n p R).toRingHom) := by
  intro q
  refine ⟨PrimeSpectrum.comap (restrictCoordinates n R).toRingHom q, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  have h := congrArg AlgHom.toRingHom (restrict_comp_normalize n p R)
  change PrimeSpectrum.comap
    ((restrictCoordinates n R).comp (normalizeCoordinates n p R)).toRingHom q = q
  rw [h]
  rfl

include p in
/-- Over a field the actual special-linear scheme is connected. -/
theorem connectedSpace_groupScheme (K : Type u) [Field K] :
    ConnectedSpace (groupScheme n (CommRingCat.of K)).X.left := by
  change ConnectedSpace (PrimeSpectrum (CoordinateRing n K))
  have : ConnectedSpace (PrimeSpectrum (GeneralLinear.CoordinateRing n K)) := inferInstance
  exact (comap_normalizeCoordinates_surjective n p K).connectedSpace
    (PrimeSpectrum.continuous_comap _)

end Schemes

end Langlands.GroupScheme.SpecialLinear
