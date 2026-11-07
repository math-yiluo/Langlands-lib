import Langlands.GroupScheme.MatrixRepresentation.OrderedAdditiveCoordinates
import Langlands.GroupScheme.MatrixRepresentation.OrderedAdditiveTruncation
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusCoordinateModel
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Ordered distributions on the actual Frobenius-origin quotient -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusOrderedDistributions

open OrderedAdditiveProducts OrderedAdditiveCoordinates OrderedAdditiveTruncation
open FrobeniusCoordinateModel FrobeniusPolynomialBox
open Langlands.Algebra.PolynomialBoxQuotient

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (.of k))} [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)

/-- The intrinsic Frobenius-origin condition on an actual affine point. -/
def IsOriginPoint (A : CommAlgCat.{u} k) (g : G.affinePoints A) : Prop :=
  ∀ a ∈ CoordinateWeights.augmentationIdeal G,
    (Lie.pointCoordinates G g a) ^ p ^ r = 0

variable {d : ℕ}
    (x : Fin d → (VectorGroup.groupScheme (.of k) 1 ⟶ G))
    (hx : Function.Bijective (coordinateMap x))

include hx in
/-- Bijective actual ordered coordinates identify the intrinsic origin condition
with the exact nilpotence condition on every parameter. -/
theorem isOriginPoint_orderedPoint_iff (A : CommAlgCat.{u} k) (t : Fin d → A) :
    IsOriginPoint p r A (orderedPoint x A t) ↔
      ∀ i, t i ^ p ^ r = 0 := by
  constructor
  · intro h i
    let a := (coordinateEquiv x hx).symm (MvPolynomial.X i)
    have hmap : coordinateMap x a = MvPolynomial.X i :=
      (coordinateEquiv x hx).apply_symm_apply _
    have ha : a ∈ CoordinateWeights.augmentationIdeal G := by
      change Lie.coordinateOrigin G a = 0
      rw [← coordinateMap_origin x, hmap]
      exact MvPolynomial.constantCoeff_X k i
    have hpow := h a ha
    rw [pointCoordinates_orderedPoint, AlgHom.comp_apply, hmap,
      MvPolynomial.aeval_X] at hpow
    exact hpow
  · intro ht a ha
    change Lie.coordinateOrigin G a = 0 at ha
    rw [pointCoordinates_orderedPoint, AlgHom.comp_apply,
      aeval_pow_eq_origin p d r t ht, coordinateMap_origin, ha, map_zero]
    exact zero_pow (pow_ne_zero _ (expChar_ne_zero k p))

/-- The canonical ordered coordinates identify the actual Frobenius quotient
with the explicit polynomial box. -/
def orderedModelEquiv :
    quotientAlgebra G p r ≃ₐ[k] boxAlgebra (k := k) (bound p d r) :=
  polynomialModelEquiv G p r (coordinateEquiv x hx) (coordinateMap_origin x)

@[simp]
theorem orderedModelEquiv_quotientMap (a : CharacterUnits.Coord G) :
    orderedModelEquiv p r x hx (quotientMap G p r a) =
      Ideal.Quotient.mkₐ k (boxIdeal (bound p d r)) (coordinateMap x a) := rfl

/-- All retained ordered coefficients of an element of the actual quotient. -/
def coordinateCoefficientsEquiv :
    quotientAlgebra G p r ≃ₗ[k] (Set.Iic (bound p d r) → k) :=
  (orderedModelEquiv p r x hx).toLinearEquiv.trans (coefficientsEquiv (bound p d r))

@[simp]
theorem coordinateCoefficientsEquiv_quotientMap
    (a : CharacterUnits.Coord G) (b : Set.Iic (bound p d r)) :
    coordinateCoefficientsEquiv p r x hx (quotientMap G p r a) b =
      (coordinateMap x a).coeff b.val := by
  change coefficient (bound p d r) b.val b.property
    (orderedModelEquiv p r x hx (quotientMap G p r a)) = _
  rw [orderedModelEquiv_quotientMap, coefficient_mk]

/-- The monomial coordinate basis of the actual Frobenius quotient. -/
def coordinateBasis :
    Module.Basis (Set.Iic (bound p d r)) k (quotientAlgebra G p r) :=
  Module.Basis.ofEquivFun (coordinateCoefficientsEquiv p r x hx)

@[simp]
theorem coordinateBasis_repr_quotientMap
    (a : CharacterUnits.Coord G) (b : Set.Iic (bound p d r)) :
    (coordinateBasis p r x hx).repr (quotientMap G p r a) b =
      (coordinateMap x a).coeff b.val := by
  exact coordinateCoefficientsEquiv_quotientMap p r x hx a b

/-- The dual basis consists of the retained ordered coefficient distributions. -/
def distributionBasis :
    Module.Basis (Set.Iic (bound p d r)) k
      (Module.Dual k (quotientAlgebra G p r)) := by
  classical
  exact (coordinateBasis p r x hx).dualBasis

@[simp]
theorem distributionBasis_quotientMap
    (b : Set.Iic (bound p d r)) (a : CharacterUnits.Coord G) :
    distributionBasis p r x hx b (quotientMap G p r a) =
      (coordinateMap x a).coeff b.val := by
  classical
  rw [distributionBasis, Module.Basis.dualBasis_apply,
    coordinateBasis_repr_quotientMap]

variable {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)

/-- Linear coefficients of the original action at the actual quotient point. -/
def distributionAction :
    Module.Dual k (quotientAlgebra G p r) →ₗ[k] Module.End k (n → k) :=
  (Matrix.toLin' : Matrix n n k ≃ₗ[k] Module.End k (n → k)).toLinearMap.comp
    ({ toFun := fun ℓ =>
        (ρ.affineMatrix (quotientAlgebra G p r) (quotientPoint G p r) :
          Matrix n n (quotientAlgebra G p r)).map ℓ
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } :
        Module.Dual k (quotientAlgebra G p r) →ₗ[k] Matrix n n k)

/-- Each actual quotient distribution acts as precisely the corresponding
ordered product of restricted divided powers. -/
theorem distributionAction_basis (b : Set.Iic (bound p d r)) :
    distributionAction p r ρ (distributionBasis p r x hx b) =
      coefficientOperator ρ x b.val := by
  have hM :
      (ρ.affineMatrix (quotientAlgebra G p r) (quotientPoint G p r) :
          Matrix n n (quotientAlgebra G p r)).map (distributionBasis p r x hx b) =
        Matrix.of fun i j => (actionPolynomial ρ x i j).coeff b.val := by
    rw [affineMatrix_quotientPoint]
    ext i j
    change distributionBasis p r x hx b
      (quotientMap G p r (ρ.universalCharacterMatrix i j)) = _
    rw [distributionBasis_quotientMap]
    exact congrArg (fun M : Matrix n n (MvPolynomial (Fin d) k) =>
      (M i j).coeff b.val) (universalCharacterMatrix_coordinateMap x ρ)
  change Matrix.toLin'
    ((ρ.affineMatrix (quotientAlgebra G p r) (quotientPoint G p r) :
      Matrix n n (quotientAlgebra G p r)).map
        (distributionBasis p r x hx b)) = _
  rw [hM]
  exact orderedCoefficients_eq_prod ρ x b.val

include hx in
/-- The whole actual quotient dual has exactly the bounded ordered divided-power
operator span as its image. -/
theorem range_distributionAction :
    LinearMap.range (distributionAction p r ρ) =
      Submodule.span k (Set.range fun b : Set.Iic (bound p d r) =>
        coefficientOperator ρ x b.val) := by
  have h := congrArg (Submodule.map (distributionAction p r ρ))
    (distributionBasis p r x hx).span_eq
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at h
  simpa only [Function.comp_def, distributionAction_basis] using h.symm

/-- The span generated by all scalar contractions of the actual intrinsic
Frobenius-origin orbit, over all commutative test algebras. -/
def originOrbitSpan (v : n → k) : Submodule k (n → k) :=
  Submodule.span k {w | ∃ (A : CommAlgCat.{u} k) (g : G.affinePoints A),
    IsOriginPoint p r A g ∧ ∃ ℓ : A →ₗ[k] k,
      w = fun i => ℓ (ρ.affineAction A g
        (fun j => algebraMap k A (v j)) i)}

include hx in
/-- Intrinsic origin points and ordered nilpotent tuples give exactly the same
actual orbit span, retaining arbitrary nonreduced test algebras. -/
theorem originOrbitSpan_eq_nilpotentOrbitSpan (v : n → k) :
    originOrbitSpan p r ρ v =
      nilpotentOrbitSpan ρ x (bound p d r) v := by
  apply congrArg (Submodule.span k)
  ext w
  constructor
  · rintro ⟨A, g, hg, ℓ, hw⟩
    obtain ⟨t, rfl⟩ := (orderedPoint_bijective x hx A).surjective g
    refine ⟨A, t, ?_, ℓ, hw⟩
    intro i
    rw [bound_add_one (k := k)]
    exact (isOriginPoint_orderedPoint_iff p r x hx A t).mp hg i
  · rintro ⟨A, t, ht, ℓ, hw⟩
    refine ⟨A, orderedPoint x A t, ?_, ℓ, hw⟩
    apply (isOriginPoint_orderedPoint_iff p r x hx A t).mpr
    intro i
    rw [← bound_add_one (k := k) p d r i]
    exact ht i

include hx in
/-- The intrinsic actual Frobenius-origin orbit span is the span of precisely
the bounded ordered divided-power images. -/
theorem originOrbitSpan_eq (v : n → k) :
    originOrbitSpan p r ρ v =
      Submodule.span k (Set.range fun b : Set.Iic (bound p d r) =>
        coefficientOperator ρ x b.val v) := by
  rw [originOrbitSpan_eq_nilpotentOrbitSpan p r x hx ρ,
    nilpotentOrbitSpan_eq]

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusOrderedDistributions
