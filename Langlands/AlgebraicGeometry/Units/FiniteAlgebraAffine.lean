import Langlands.AlgebraicGeometry.Units.FiniteAlgebraRepresentabilityStatement
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.FiniteAlgebraUnits

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
  {n : ℕ} (b : Module.Basis (Fin n) k A)

lemma candidate_smooth : Smooth (candidate b).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (candidateRing b))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap k (candidateRing b)).Smooth
  rw [RingHom.smooth_algebraMap]
  let : Algebra.Smooth (coordinateRing k n) (candidateRing b) :=
    Algebra.Smooth.of_isLocalization_Away (determinant b)
  exact Algebra.Smooth.comp k (coordinateRing k n) (candidateRing b)

variable {B : Type u} [CommRing B] [Algebra k B]

/-- Evaluate the generic element under a polynomial coefficient map. -/
def evaluatedElement (φ : coordinateRing k n →ₐ[k] B) : B ⊗[k] A :=
  Algebra.TensorProduct.map φ (AlgHom.id k A) (genericElement b)

lemma evaluatedElement_eq_sum (φ : coordinateRing k n →ₐ[k] B) :
    evaluatedElement b φ = ∑ i, φ (MvPolynomial.X i) ⊗ₜ[k] b i := by
  simp [evaluatedElement, genericElement]

@[simp]
lemma evaluatedElement_repr (φ : coordinateRing k n →ₐ[k] B) (i : Fin n) :
    (b.baseChange B).repr (evaluatedElement b φ) i = φ (MvPolynomial.X i) := by
  simp [evaluatedElement_eq_sum, map_sum, Module.Basis.repr_self, Finsupp.single_apply]

lemma evaluatedElement_injective : Function.Injective (evaluatedElement b (B := B)) := by
  intro φ ψ h
  apply MvPolynomial.algHom_ext
  intro i
  simpa using congrArg (fun x => (b.baseChange B).repr x i) h

/-- The coefficient homomorphism determined by a tensor element. -/
def coefficientMap (x : B ⊗[k] A) : coordinateRing k n →ₐ[k] B :=
  MvPolynomial.aeval fun i => (b.baseChange B).repr x i

@[simp]
lemma evaluatedElement_coefficientMap (x : B ⊗[k] A) :
    evaluatedElement b (coefficientMap b x) = x := by
  apply (b.baseChange B).repr.injective
  ext i
  simp [coefficientMap]

lemma norm_evaluatedElement (φ : coordinateRing k n →ₐ[k] B) :
    Algebra.norm B (evaluatedElement b φ) = φ (determinant b) :=
  norm_map b φ (genericElement b)

lemma coefficientMap_determinant_isUnit (x : (B ⊗[k] A)ˣ) :
    IsUnit (coefficientMap b (x : B ⊗[k] A) (determinant b)) := by
  let := Module.Free.of_basis (b.baseChange B)
  let := Module.Finite.of_basis (b.baseChange B)
  rw [← norm_evaluatedElement, evaluatedElement_coefficientMap]
  exact (LinearMap.isUnit_iff_isUnit_det _).mp
    ((Algebra.lmul_isUnit_iff (R := B)).mpr x.isUnit)

/-- The unique localization map encoded by a unit tensor. -/
def unitCoefficientMap (x : (B ⊗[k] A)ˣ) : candidateRing b →ₐ[k] B :=
  IsLocalization.Away.liftAlgHom (determinant b) (coefficientMap_determinant_isUnit b x)

@[simp]
lemma unitCoefficientMap_algebraMap (x : (B ⊗[k] A)ˣ) (r : coordinateRing k n) :
    unitCoefficientMap b x (algebraMap (coordinateRing k n) (candidateRing b) r) =
      coefficientMap b (x : B ⊗[k] A) r := by
  exact IsLocalization.Away.lift_eq (determinant b)
    (coefficientMap_determinant_isUnit b x) r

/-- Pull back the algebraic universal unit by a candidate-ring homomorphism. -/
def algebraicPoint (φ : candidateRing b →ₐ[k] B) : (B ⊗[k] A)ˣ :=
  Units.map (Algebra.TensorProduct.map φ (AlgHom.id k A)).toMonoidHom
    (algebraicUniversalUnit b)

lemma algebraicPoint_val (φ : candidateRing b →ₐ[k] B) :
    (algebraicPoint b φ : B ⊗[k] A) =
      evaluatedElement b (φ.comp (Algebra.algHom k (coordinateRing k n) (candidateRing b))) := by
  simp [algebraicPoint, algebraicUniversalUnit_val, localizedGenericElement_eq_sum,
    evaluatedElement_eq_sum, Algebra.algHom]

@[simp]
lemma algebraicPoint_unitCoefficientMap (x : (B ⊗[k] A)ˣ) :
    algebraicPoint b (unitCoefficientMap b x) = x := by
  apply Units.ext
  rw [algebraicPoint_val]
  have h : (unitCoefficientMap b x).comp
      (Algebra.algHom k (coordinateRing k n) (candidateRing b)) =
      coefficientMap b (x : B ⊗[k] A) := by
    apply AlgHom.ext
    intro r
    exact unitCoefficientMap_algebraMap b x r
  rw [h, evaluatedElement_coefficientMap]

lemma algebraicPoint_injective : Function.Injective (algebraicPoint b (B := B)) := by
  intro φ ψ h
  apply IsLocalization.algHom_ext (Submonoid.powers (determinant b))
  apply evaluatedElement_injective b
  simpa only [algebraicPoint_val] using congrArg Units.val h

/-- Finite-free determinant coordinates represent units on every algebra. -/
def algebraicPointEquiv : (candidateRing b →ₐ[k] B) ≃ (B ⊗[k] A)ˣ where
  toFun := algebraicPoint b
  invFun := unitCoefficientMap b
  left_inv _φ := algebraicPoint_injective b (algebraicPoint_unitCoefficientMap b _)
  right_inv := algebraicPoint_unitCoefficientMap b

end Langlands.AlgebraicGeometry.FiniteAlgebraUnits
