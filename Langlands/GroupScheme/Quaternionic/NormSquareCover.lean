import Langlands.Algebra.ReducedNorm
import Mathlib.GroupTheory.NoncommCoprod

/-!
# The norm-square cover on coefficient algebras

The group of pairs `(a,t)` satisfying `Nrd(a) = t²` is the direct product of
the reduced-norm-one group and the scalar units in reduced degree two.
This construction does not assert a comparison with a spin group.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open scoped TensorProduct

namespace Langlands.CentralSimple

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  (R : Type v) [CommRing R] [Algebra K R]

/-- Central scalar units in the scalar-extended algebra. -/
def normCoverScalarUnits : Rˣ →* (R ⊗[K] A)ˣ :=
  Units.map (algebraMap R (R ⊗[K] A)).toMonoidHom

@[simp] theorem normCoverScalarUnits_val (t : Rˣ) :
    (normCoverScalarUnits K A R t : R ⊗[K] A) = (t : R) ⊗ₜ[K] (1 : A) := rfl

/-- The scalar units commute with every tensor unit. -/
theorem normCoverScalarUnits_commute (t : Rˣ) (a : (R ⊗[K] A)ˣ) :
    Commute (normCoverScalarUnits K A R t) a := by
  apply Units.ext
  exact Algebra.commutes (t : R) (a : R ⊗[K] A)

variable [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- The actual group of pairs of units with reduced norm equal to a square. -/
def normSquareCover : Subgroup ((R ⊗[K] A)ˣ × Rˣ) where
  carrier := {x | reducedNormUnits K A R x.1 = x.2 ^ 2}
  one_mem' := by
    change reducedNormUnits K A R 1 = (1 : Rˣ) ^ 2
    simp
  mul_mem' := by
    intro x y hx hy
    change reducedNormUnits K A R (x.1 * y.1) = (x.2 * y.2) ^ 2
    rw [map_mul, hx, hy, mul_pow]
  inv_mem' := by
    intro x hx
    change reducedNormUnits K A R x.1⁻¹ = (x.2⁻¹) ^ 2
    rw [map_inv, hx, inv_pow]

@[simp] theorem mem_normSquareCover (x : (R ⊗[K] A)ˣ × Rˣ) :
    x ∈ normSquareCover K A R ↔ reducedNormUnits K A R x.1 = x.2 ^ 2 := Iff.rfl

/-- Projection of the pair to its algebra unit. -/
def normSquareProjection : normSquareCover K A R →* (R ⊗[K] A)ˣ :=
  (MonoidHom.fst _ _).comp (normSquareCover K A R).subtype

/-- The chosen square root of the reduced norm. -/
def normSquareRoot : normSquareCover K A R →* Rˣ :=
  (MonoidHom.snd _ _).comp (normSquareCover K A R).subtype

@[simp] theorem normSquareProjection_apply (x : normSquareCover K A R) :
    normSquareProjection K A R x = x.val.1 := rfl

@[simp] theorem normSquareRoot_apply (x : normSquareCover K A R) :
    normSquareRoot K A R x = x.val.2 := rfl

/-- A cover point comes with an actual square root of its reduced norm. -/
theorem normSquareProjection_norm (x : normSquareCover K A R) :
    reducedNormUnits K A R (normSquareProjection K A R x) =
      normSquareRoot K A R x ^ 2 := x.property

/-- Exactly the units of square reduced norm occur in the image. -/
theorem mem_range_normSquareProjection (a : (R ⊗[K] A)ˣ) :
    a ∈ (normSquareProjection K A R).range ↔
      ∃ t : Rˣ, reducedNormUnits K A R a = t ^ 2 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨normSquareRoot K A R x, normSquareProjection_norm K A R x⟩
  · rintro ⟨t, ht⟩
    exact ⟨⟨(a, t), ht⟩, rfl⟩

/-- The norm-one factor enters with square-root coordinate one. -/
def normSquareNormOneLift : reducedNormOne K A R →* normSquareCover K A R where
  toFun a := ⟨(a.val, 1), by
    change reducedNormUnits K A R a.val = (1 : Rˣ) ^ 2
    have ha : reducedNormUnits K A R a.val = 1 := a.property
    simpa only [one_pow] using ha⟩
  map_one' := rfl
  map_mul' _ _ := by apply Subtype.ext; simp

@[simp] theorem normSquareNormOneLift_val (a : reducedNormOne K A R) :
    (normSquareNormOneLift K A R a).val = (a.val, 1) := rfl

variable (hdegree : reducedDegree K A = 2)

include hdegree

/-- In reduced degree two the scalar norm is the square. -/
theorem reducedNormUnits_normCoverScalarUnits (t : Rˣ) :
    reducedNormUnits K A R (normCoverScalarUnits K A R t) = t ^ 2 := by
  apply Units.ext
  change reducedNorm K A R ((t : R) ⊗ₜ[K] (1 : A)) = (t : R) ^ 2
  rw [reducedNorm_scalar, hdegree]

/-- The scalar factor enters with its own value as square-root coordinate. -/
def normSquareScalarLift : Rˣ →* normSquareCover K A R where
  toFun t := ⟨(normCoverScalarUnits K A R t, t),
    reducedNormUnits_normCoverScalarUnits K A R hdegree t⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' _ _ := by apply Subtype.ext; simp

@[simp] theorem normSquareScalarLift_val (t : Rˣ) :
    (normSquareScalarLift K A R hdegree t).val =
      (normCoverScalarUnits K A R t, t) := rfl

/-- The two lifted factors commute, including on nonreduced coefficient algebras. -/
theorem normSquare_lifts_commute (a : reducedNormOne K A R) (t : Rˣ) :
    Commute (normSquareNormOneLift K A R a) (normSquareScalarLift K A R hdegree t) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (normCoverScalarUnits_commute K A R t a.val).symm.eq
  · simp

/-- Multiplication of the norm-one and scalar lifts. -/
def normSquareProduct : reducedNormOne K A R × Rˣ →* normSquareCover K A R :=
  (normSquareNormOneLift K A R).noncommCoprod
    (normSquareScalarLift K A R hdegree) (normSquare_lifts_commute K A R hdegree)

@[simp] theorem normSquareProduct_val (a : reducedNormOne K A R) (t : Rˣ) :
    (normSquareProduct K A R hdegree (a, t)).val =
      (a.val * normCoverScalarUnits K A R t, t) := by
  simp [normSquareProduct, MonoidHom.noncommCoprod_apply]

/-- Dividing by the scalar square root gives a unit of reduced norm one. -/
def normSquareNormOnePart (x : normSquareCover K A R) : reducedNormOne K A R :=
  ⟨x.val.1 * (normCoverScalarUnits K A R x.val.2)⁻¹, by
    change reducedNormUnits K A R
      (x.val.1 * (normCoverScalarUnits K A R x.val.2)⁻¹) = 1
    rw [map_mul, map_inv, reducedNormUnits_normCoverScalarUnits K A R hdegree,
      x.property, mul_inv_cancel]⟩

/-- The norm-square cover is the actual direct product of norm-one and scalar units. -/
def normSquareProductEquiv :
    reducedNormOne K A R × Rˣ ≃* normSquareCover K A R where
  toFun := normSquareProduct K A R hdegree
  invFun x := (normSquareNormOnePart K A R hdegree x, x.val.2)
  left_inv x := by
    rcases x with ⟨a, t⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [normSquareNormOnePart]
    · simp
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · change (x.val.1 * (normCoverScalarUnits K A R x.val.2)⁻¹) *
        normCoverScalarUnits K A R x.val.2 = x.val.1
      exact inv_mul_cancel_right _ _
    · simp
  map_mul' := (normSquareProduct K A R hdegree).map_mul

/-- Containment of both actual lifted factors suffices for full generation. -/
theorem normSquareCover_eq_top_of_lifts (N : Subgroup (normSquareCover K A R))
    (hone : ∀ a, normSquareNormOneLift K A R a ∈ N)
    (hscalar : ∀ t, normSquareScalarLift K A R hdegree t ∈ N) :
    N = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨⟨a, t⟩, rfl⟩ := (normSquareProductEquiv K A R hdegree).surjective x
  exact N.mul_mem (hone a) (hscalar t)

end Langlands.CentralSimple
