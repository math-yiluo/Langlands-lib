import Langlands.GroupScheme.AffineWeilRestrictionMaps
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.KernelSquareTransport
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Vector coordinates for affine Weil restriction along a finite free algebra -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {n : ℕ} (b : Module.Basis (Fin n) A B)

/-- Coordinates of a scalar extension in a specified finite basis. -/
def tensorCoordinateEquiv (T : Type u) [CommRing T] [Algebra A T] :
    (Fin n → T) ≃+ B ⊗[A] T :=
  (Algebra.TensorProduct.basis T b).equivFun.symm.toAddEquiv.trans
    (TensorProduct.comm A T B).toAddEquiv

theorem tensorCoordinateEquiv_apply (T : Type u) [CommRing T] [Algebra A T]
    (x : Fin n → T) :
    tensorCoordinateEquiv b T x = ∑ j, b j ⊗ₜ[A] x j := by
  change (TensorProduct.comm A T B) ((Algebra.TensorProduct.basis T b).equivFun.symm x) = _
  simp only [Module.Basis.equivFun_symm_apply, Algebra.TensorProduct.basis_apply, map_sum,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.comm_tmul]

/-- Basis coordinates commute with arbitrary maps of coefficient algebras. -/
theorem lTensor_tensorCoordinateEquiv
    {T T' : Type u} [CommRing T] [CommRing T'] [Algebra A T] [Algebra A T']
    (f : T →ₐ[A] T') (x : Fin n → T) :
    Algebra.TensorProduct.lTensor (S := B) B f (tensorCoordinateEquiv b T x) =
      tensorCoordinateEquiv b T' (fun j => f (x j)) := by
  rw [tensorCoordinateEquiv_apply, tensorCoordinateEquiv_apply, map_sum]
  simp

theorem tensorCoordinateEquiv_symm_lTensor
    {T T' : Type u} [CommRing T] [CommRing T'] [Algebra A T] [Algebra A T']
    (f : T →ₐ[A] T') (x : B ⊗[A] T) :
    (tensorCoordinateEquiv b T').symm
        (Algebra.TensorProduct.lTensor (S := B) B f x) =
      fun j => f ((tensorCoordinateEquiv b T).symm x j) := by
  apply (tensorCoordinateEquiv b T').injective
  rw [AddEquiv.apply_symm_apply, ← lTensor_tensorCoordinateEquiv,
    AddEquiv.apply_symm_apply]

variable (A B) (m : ℕ)

local instance vector_isAffine :
    IsAffine (VectorGroup.groupScheme (CommRingCat.of B) m).X.left := by
  change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin m) B)))
  infer_instance

local instance vector_locallyOfFiniteType :
    LocallyOfFiniteType (VectorGroup.groupScheme (CommRingCat.of B) m).X.hom := by
  have : Smooth (VectorGroup.groupScheme (CommRingCat.of B) m).X.hom :=
    Corepresented.smooth_groupScheme_iff.mpr inferInstance
  infer_instance

/-- The finite coordinate array of a vector with tensor coefficients. -/
def tensorVectorEquiv (T : Type u) [CommRing T] [Algebra A T] :
    Multiplicative (Fin m → B ⊗[A] T) ≃* Multiplicative (Fin (m * n) → T) where
  toFun x := Multiplicative.ofAdd fun i =>
    (tensorCoordinateEquiv b T).symm (x.toAdd (finProdFinEquiv.symm i).1)
      (finProdFinEquiv.symm i).2
  invFun x := Multiplicative.ofAdd fun i =>
    tensorCoordinateEquiv b T (fun j => x.toAdd (finProdFinEquiv (i, j)))
  left_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    dsimp only [toAdd_ofAdd]
    simp only [Equiv.symm_apply_apply]
    exact AddEquiv.apply_symm_apply _ _
  right_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_ofAdd, AddEquiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    change (tensorCoordinateEquiv b T).symm
      (x.toAdd (finProdFinEquiv.symm i).1 + y.toAdd (finProdFinEquiv.symm i).1)
        (finProdFinEquiv.symm i).2 = _
    rw [map_add]
    rfl

/-- Basis coordinates of the original tensor-valued additive point group. -/
def vectorAffineCoordinates (T : CommAlgCat.{u} (CommRingCat.of A)) :
    (pointFunctor A B (VectorGroup.groupScheme (CommRingCat.of B) m)).obj T ≃*
      Multiplicative (Fin (m * n) → T) :=
  (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of B) m)
    (VectorGroup.corepresentableBy (CommRingCat.of B) m)
    ((tensorFunctor A B).obj T)).trans (tensorVectorEquiv A B b m T)

theorem vectorAffineCoordinates_naturality
    {T T' : CommAlgCat.{u} (CommRingCat.of A)} (f : T ⟶ T')
    (x : (pointFunctor A B (VectorGroup.groupScheme (CommRingCat.of B) m)).obj T) :
    vectorAffineCoordinates A B b m T'
        ((pointFunctor A B (VectorGroup.groupScheme (CommRingCat.of B) m)).map f x) =
      Multiplicative.ofAdd (fun i => f.hom ((vectorAffineCoordinates A B b m T x).toAdd i)) := by
  change tensorVectorEquiv A B b m T'
    ((Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of B) m)
      (VectorGroup.corepresentableBy (CommRingCat.of B) m) ((tensorFunctor A B).obj T'))
      ((algSpec (CommRingCat.of B)).map ((tensorFunctor A B).map f).op ≫ x)) = _
  rw [Corepresented.affinePointsEquiv_naturality]
  apply Multiplicative.toAdd.injective
  funext i
  exact congrFun (tensorCoordinateEquiv_symm_lTensor b f.hom _) (finProdFinEquiv.symm i).2

variable [Module.Finite A B] [Module.Projective A B]

/-- Natural vector coordinates on every scheme test of the actual restriction. -/
def vectorCoordinates (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ (groupScheme A B (VectorGroup.groupScheme (CommRingCat.of B) m)).X) ≃*
      Multiplicative (Fin (m * n) → Γ(T.left, ⊤)) :=
  (Corepresented.pointsEquiv
    (pointFunctor A B (VectorGroup.groupScheme (CommRingCat.of B) m))
    (corepresentableBy A B (VectorGroup.groupScheme (CommRingCat.of B) m)) T).trans
      (vectorAffineCoordinates A B b m (((algΓ (CommRingCat.of A)).obj T).unop))

theorem vectorCoordinates_naturality {T T' : Over (Spec (CommRingCat.of A))}
    (a : T' ⟶ T)
    (x : T ⟶ (groupScheme A B (VectorGroup.groupScheme (CommRingCat.of B) m)).X) :
    (vectorCoordinates A B b m T' (a ≫ x)).toAdd =
      fun i => a.left.appTop ((vectorCoordinates A B b m T x).toAdd i) := by
  dsimp only [vectorCoordinates, MulEquiv.trans_apply]
  rw [Corepresented.pointsEquiv_naturality]
  exact congrArg Multiplicative.toAdd
    (vectorAffineCoordinates_naturality A B b m (((algΓ (CommRingCat.of A)).map a).unop) _)

/-- Finite free restriction of the vector group has the expected vector dimension. -/
def vectorIso :
    groupScheme A B (VectorGroup.groupScheme (CommRingCat.of B) m) ≅
      VectorGroup.groupScheme (CommRingCat.of A) (m * n) :=
  isoOfPoints
    (fun T => (vectorCoordinates A B b m T).trans
      (VectorGroup.coordinates (CommRingCat.of A) (m * n) T).symm)
    (by
      intro T T' a x
      apply (VectorGroup.coordinates (CommRingCat.of A) (m * n) T').injective
      apply Multiplicative.toAdd.injective
      dsimp only [MulEquiv.trans_apply]
      rw [MulEquiv.apply_symm_apply, VectorGroup.coordinates_comp,
        MulEquiv.apply_symm_apply]
      exact vectorCoordinates_naturality A B b m a x)

include b in
/-- The all-test vector-group predicate holds over any base ring. -/
theorem vector_isVectorGroupOfDimension :
    RelativeRoot.IsVectorGroupOfDimension
      (groupScheme A B (VectorGroup.groupScheme (CommRingCat.of B) m)) (m * n) :=
  ⟨vectorCoordinates A B b m, fun _ _ a x => vectorCoordinates_naturality A B b m a x⟩

end Langlands.GroupScheme.AffineWeil

namespace Langlands.GroupScheme.AffineWeil

variable (k B : Type u) [Field k] [CommRing B] [Algebra k B]
  [Module.Finite k B] [Module.Projective k B] {n : ℕ}
  (b : Module.Basis (Fin n) k B) (m : ℕ)

attribute [local instance] vector_isAffine vector_locallyOfFiniteType

include b in
/-- Finite free restriction of a vector group has all three kernel properties. -/
theorem vector_properties :
    Smooth (groupScheme k B (VectorGroup.groupScheme (CommRingCat.of B) m)).X.hom ∧
      ConnectedSpace (groupScheme k B (VectorGroup.groupScheme (CommRingCat.of B) m)).X.left ∧
        IsUnipotent (groupScheme k B (VectorGroup.groupScheme (CommRingCat.of B) m)) := by
  have h := vector_isVectorGroupOfDimension k B b m
  exact ⟨h.smooth, h.connectedSpace, h.isUnipotent⟩

end Langlands.GroupScheme.AffineWeil
