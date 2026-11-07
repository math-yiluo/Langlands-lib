import Langlands.AlgebraicGeometry.Units.FiniteAlgebraAffine
import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.GaloisPointRational

/-! # Actual unit group schemes of finite-dimensional, possibly noncommutative algebras -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteAlgebraUnits

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- The ground-field spectrum. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} := Spec (CommRingCat.of k)

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

variable {C : Type u} [CommRing C] [Algebra k C]

/-- Specializing the universal unit commutes with every coefficient-algebra map. -/
theorem algebraicPoint_comp (φ : candidateRing b →ₐ[k] B) (f : B →ₐ[k] C) :
    algebraicPoint b (f.comp φ) =
      Units.map (Algebra.TensorProduct.map f (AlgHom.id k A)).toMonoidHom
        (algebraicPoint b φ) := by
  apply Units.ext
  simp [algebraicPoint_val, evaluatedElement_eq_sum]

variable (k A) in
/-- The actual unit functor of a possibly noncommutative finite algebra. -/
def functor : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u} where
  obj R := GrpCat.of (R ⊗[k] A)ˣ
  map f := GrpCat.ofHom (Units.map
    (Algebra.TensorProduct.map f.hom (AlgHom.id k A)).toMonoidHom)
  map_id R := by
    ext x
    simp
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Units.ext
    exact AlgHom.congr_fun
      (Algebra.TensorProduct.map_comp g.hom f.hom (AlgHom.id k A) (AlgHom.id k A)) x

/-- The determinant-open coordinate ring as a commutative base algebra. -/
abbrev coordinateAlgebra : CommAlgCat.{u} (CommRingCat.of k) :=
  CommAlgCat.of (CommRingCat.of k) (candidateRing b)

/-- The actual determinant-open coordinates corepresent the possibly noncommutative units. -/
def corepresentableBy :
    (functor k A ⋙ forget GrpCat).CorepresentableBy (coordinateAlgebra b) where
  homEquiv :=
    { toFun := fun φ => algebraicPoint b φ.hom
      invFun := fun x => CommAlgCat.ofHom (unitCoefficientMap b x)
      left_inv := fun φ => CommAlgCat.hom_ext ((algebraicPointEquiv b).left_inv φ.hom)
      right_inv := algebraicPoint_unitCoefficientMap b }
  homEquiv_comp f φ := algebraicPoint_comp b φ.hom f.hom

/-- The actual affine group scheme of units of the finite-dimensional algebra. -/
abbrev groupScheme : GroupScheme (base k) :=
  Corepresented.groupScheme (functor k A) (corepresentableBy b)

/-- The constructed unit group has exactly the determinant-open underlying relative scheme. -/
theorem groupScheme_X : (groupScheme b).X = candidate b := rfl

instance groupScheme_isAffine : IsAffine (groupScheme b).X.left := by
  change IsAffine (Spec (CommRingCat.of (candidateRing b)))
  infer_instance

instance groupScheme_smooth : Smooth (groupScheme b).X.hom := candidate_smooth b

/-- Affine coefficient points recover the actual units of the scalar-extended algebra. -/
def affinePointsEquiv (R : CommAlgCat.{u} (CommRingCat.of k)) :
    ((algSpec (CommRingCat.of k)).obj (op R) ⟶ (groupScheme b).X) ≃* (R ⊗[k] A)ˣ :=
  Corepresented.affinePointsEquiv (functor k A) (corepresentableBy b) R

/-- On every test scheme, actual points are units over its actual relative global sections. -/
def pointsEquiv (T : Over (base k)) :
    (T ⟶ (groupScheme b).X) ≃*
      (((algΓ (CommRingCat.of k)).obj T).unop ⊗[k] A)ˣ :=
  Corepresented.pointsEquiv (functor k A) (corepresentableBy b) T

/-- The affine comparison respects every actual change of coefficient algebra. -/
theorem affinePointsEquiv_naturality {R S : CommAlgCat.{u} (CommRingCat.of k)}
    (f : R ⟶ S) (x : (algSpec (CommRingCat.of k)).obj (op R) ⟶ (groupScheme b).X) :
    affinePointsEquiv b S ((algSpec (CommRingCat.of k)).map f.op ≫ x) =
      Units.map (Algebra.TensorProduct.map f.hom (AlgHom.id k A)).toMonoidHom
        (affinePointsEquiv b R x) :=
  Corepresented.affinePointsEquiv_naturality (functor k A) (corepresentableBy b) f x

/-- The all-test comparison respects the actual relative section pullback. -/
theorem pointsEquiv_naturality {T T' : Over (base k)} (f : T' ⟶ T)
    (x : T ⟶ (groupScheme b).X) :
    pointsEquiv b T' (f ≫ x) =
      Units.map (Algebra.TensorProduct.map
        (((algΓ (CommRingCat.of k)).map f).unop.hom) (AlgHom.id k A)).toMonoidHom
        (pointsEquiv b T x) :=
  Corepresented.pointsEquiv_naturality (functor k A) (corepresentableBy b) f x

/-- Actual rational points recover the original algebra's units by the tensor-unit comparison. -/
def rationalPointsEquiv : rationalPoints (groupScheme b) ≃* Aˣ :=
  (GaloisPointComparison.rationalCoeffEquiv k (groupScheme b)).trans
    ((affinePointsEquiv b (CommAlgCat.of (CommRingCat.of k) k)).trans
      (Units.mapEquiv (Algebra.TensorProduct.lid k A).toMulEquiv))

end Langlands.GroupScheme.FiniteAlgebraUnits
