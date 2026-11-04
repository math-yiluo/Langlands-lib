import Langlands.GroupScheme.Rational.PolynomialGaloisDescent
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Finite-Galois descent and norms of actual polynomial points -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.PolynomialPoint

open Langlands.AlgebraicGeometry.PointTopology

variable (k L : Type u) [Field k] [Field L] [Algebra k L] (I : Type u)
    (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The coefficient extension on actual multivariate polynomial points. -/
def extend :
    G.affinePoints (CommAlgCat.of k (MvPolynomial I k)) →*
      G.affinePoints (CommAlgCat.of k (MvPolynomial I L)) :=
  G.affinePointMap (CommAlgCat.ofHom (PolynomialGalois.extend k L I))

/-- Galois acts on coefficients while leaving the polynomial variables fixed. -/
def conjugate (σ : L ≃ₐ[k] L) :
    G.affinePoints (CommAlgCat.of k (MvPolynomial I L)) →*
      G.affinePoints (CommAlgCat.of k (MvPolynomial I L)) :=
  G.affinePointMap (CommAlgCat.ofHom (PolynomialGalois.conjugate k L I σ))

@[simp] theorem conjugate_one
    (x : G.affinePoints (CommAlgCat.of k (MvPolynomial I L))) :
    conjugate k L I G 1 x = x := by
  change Lie.affineMap G (PolynomialGalois.conjugate k L I 1) x = x
  rw [PolynomialGalois.conjugate_one]
  exact Lie.affineMap_id G x

@[simp] theorem conjugate_mul (σ τ : L ≃ₐ[k] L)
    (x : G.affinePoints (CommAlgCat.of k (MvPolynomial I L))) :
    conjugate k L I G (σ * τ) x =
      conjugate k L I G σ (conjugate k L I G τ x) := by
  change Lie.affineMap G (PolynomialGalois.conjugate k L I (σ * τ)) x = _
  rw [PolynomialGalois.conjugate_mul]
  exact Lie.affineMap_comp G _ _ x

/-- Coefficient conjugation is an automorphism of the actual point group. -/
def conjugateEquiv (σ : L ≃ₐ[k] L) :
    G.affinePoints (CommAlgCat.of k (MvPolynomial I L)) ≃*
      G.affinePoints (CommAlgCat.of k (MvPolynomial I L)) where
  toFun := conjugate k L I G σ
  invFun := conjugate k L I G σ⁻¹
  left_inv x := by rw [← conjugate_mul, inv_mul_cancel, conjugate_one]
  right_inv x := by rw [← conjugate_mul, mul_inv_cancel, conjugate_one]
  map_mul' := map_mul _

@[simp] theorem conjugate_extend (σ : L ≃ₐ[k] L)
    (x : G.affinePoints (CommAlgCat.of k (MvPolynomial I k))) :
    conjugate k L I G σ (extend k L I G x) = extend k L I G x := by
  change Lie.affineMap G (PolynomialGalois.conjugate k L I σ)
    (Lie.affineMap G (PolynomialGalois.extend k L I) x) = _
  rw [← Lie.affineMap_comp]
  have h : (PolynomialGalois.conjugate k L I σ).comp
      (PolynomialGalois.extend k L I) = PolynomialGalois.extend k L I := by
    apply AlgHom.ext
    exact PolynomialGalois.conjugate_extend k L I σ
  exact congrArg (fun f => Lie.affineMap G f x) h

/-- Invariant polynomial points form a subgroup. -/
def fixedSubgroup :
    Subgroup (G.affinePoints (CommAlgCat.of k (MvPolynomial I L))) where
  carrier := {x | ∀ σ : L ≃ₐ[k] L, conjugate k L I G σ x = x}
  one_mem' σ := map_one _
  mul_mem' hx hy σ := by rw [map_mul, hx σ, hy σ]
  inv_mem' hx σ := by rw [map_inv, hx σ]

section Descent

variable [IsAffine G.X.left]

@[simp] theorem coordinates_extend
    (x : G.affinePoints (CommAlgCat.of k (MvPolynomial I k)))
    (a : AffineCoordinateRing k G.X) :
    GaloisPoint.coordinates k G (MvPolynomial I L) (extend k L I G x) a =
      PolynomialGalois.extend k L I
        (GaloisPoint.coordinates k G (MvPolynomial I k) x a) := by
  simp only [GaloisPoint.coordinates_apply]
  exact G.affinePointEvaluation_map
    (CommAlgCat.ofHom (PolynomialGalois.extend k L I)) x a

@[simp] theorem coordinates_conjugate (σ : L ≃ₐ[k] L)
    (x : G.affinePoints (CommAlgCat.of k (MvPolynomial I L)))
    (a : AffineCoordinateRing k G.X) :
    GaloisPoint.coordinates k G (MvPolynomial I L) (conjugate k L I G σ x) a =
      PolynomialGalois.conjugate k L I σ
        (GaloisPoint.coordinates k G (MvPolynomial I L) x a) := by
  simp only [GaloisPoint.coordinates_apply]
  exact G.affinePointEvaluation_map
    (CommAlgCat.ofHom (PolynomialGalois.conjugate k L I σ)) x a

/-- Coefficient extension reflects equality of polynomial points of an affine group. -/
theorem extend_injective : Function.Injective (extend k L I G) := by
  intro x y h
  apply (GaloisPoint.coordinates k G (MvPolynomial I k)).injective
  apply AlgHom.ext
  intro a
  apply PolynomialGalois.extend_injective k L I
  simpa only [coordinates_extend] using
    congrArg (fun z => GaloisPoint.coordinates k G (MvPolynomial I L) z a) h

variable [FiniteDimensional k L] [IsGalois k L]

/-- Descend the invariant coordinate map, and reconstruct the actual polynomial point. -/
def descend (x : fixedSubgroup k L I G) :
    G.affinePoints (CommAlgCat.of k (MvPolynomial I k)) :=
  (GaloisPoint.coordinates k G (MvPolynomial I k)).symm
    (PolynomialGalois.descendAlgHom k L I
      (GaloisPoint.coordinates k G (MvPolynomial I L) x.val)
      (fun σ a => by
        simpa only [coordinates_conjugate] using
          congrArg (fun z => GaloisPoint.coordinates k G (MvPolynomial I L) z a)
            (x.property σ)))

@[simp] theorem extend_descend (x : fixedSubgroup k L I G) :
    extend k L I G (descend k L I G x) = x.val := by
  apply (GaloisPoint.coordinates k G (MvPolynomial I L)).injective
  apply AlgHom.ext
  intro a
  rw [coordinates_extend]
  simp only [descend, Equiv.apply_symm_apply]
  exact PolynomialGalois.extend_descendAlgHom k L I _ _ a

/-- The fixed subgroup consists exactly of base-field polynomial points. -/
theorem mem_range_extend_iff
    (x : G.affinePoints (CommAlgCat.of k (MvPolynomial I L))) :
    x ∈ Set.range (extend k L I G) ↔ x ∈ fixedSubgroup k L I G := by
  constructor
  · rintro ⟨y, rfl⟩ σ
    exact conjugate_extend k L I G σ y
  · intro hx
    exact ⟨descend k L I G ⟨x, hx⟩, extend_descend k L I G ⟨x, hx⟩⟩

/-- Effective finite-Galois descent as a multiplicative equivalence of actual points. -/
def fixedEquiv :
    G.affinePoints (CommAlgCat.of k (MvPolynomial I k)) ≃* fixedSubgroup k L I G where
  toFun x := ⟨extend k L I G x, fun σ => conjugate_extend k L I G σ x⟩
  invFun := descend k L I G
  left_inv _ := extend_injective k L I G (extend_descend k L I G _)
  right_inv x := Subtype.ext (extend_descend k L I G x)
  map_mul' x y := Subtype.ext (map_mul (extend k L I G) x y)

end Descent

local instance centerCommGroup (A : Type*) [Group A] : CommGroup (Subgroup.center A) where
  __ := (inferInstance : Group (Subgroup.center A))
  mul_comm := mul_comm'

/-- Coefficient automorphisms preserve the center of the actual polynomial-point group. -/
def centerConjugate (σ : L ≃ₐ[k] L) :
    Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I L))) →*
      Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I L))) :=
  (Subgroup.centerCongr (conjugateEquiv k L I G σ)).toMonoidHom

@[simp] theorem centerConjugate_val (σ : L ≃ₐ[k] L)
    (x : Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I L)))) :
    (centerConjugate k L I G σ x).val = conjugate k L I G σ x.val := rfl

@[simp] theorem centerConjugate_mul (σ τ : L ≃ₐ[k] L)
    (x : Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I L)))) :
    centerConjugate k L I G (σ * τ) x =
      centerConjugate k L I G σ (centerConjugate k L I G τ x) := by
  apply Subtype.ext
  exact conjugate_mul k L I G σ τ x.val

variable [FiniteDimensional k L]

/-- Take the full Galois product in the commutative center, without commuting the ambient group. -/
def conjugateProduct :
    Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I L))) →*
      Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I L))) where
  toFun x := ∏ σ : L ≃ₐ[k] L, centerConjugate k L I G σ x
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]

/-- The central Galois product is an invariant actual polynomial point. -/
theorem conjugateProduct_fixed
    (x : Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I L)))) :
    (conjugateProduct k L I G x).val ∈ fixedSubgroup k L I G := by
  intro σ
  change (centerConjugate k L I G σ (conjugateProduct k L I G x)).val = _
  apply congrArg Subtype.val
  change centerConjugate k L I G σ
      (∏ τ : L ≃ₐ[k] L, centerConjugate k L I G τ x) =
    ∏ τ : L ≃ₐ[k] L, centerConjugate k L I G τ x
  rw [map_prod]
  simp only [← centerConjugate_mul]
  exact Fintype.prod_equiv (Equiv.mulLeft σ) _ _ (fun _ => rfl)

variable [IsAffine G.X.left] [IsGalois k L]

/-- Descend the central Galois product to an actual base-field polynomial point. -/
def normPoint :
    Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I L))) →*
      G.affinePoints (CommAlgCat.of k (MvPolynomial I k)) :=
  (fixedEquiv k L I G).symm.toMonoidHom.comp
    (((Subgroup.center _).subtype.comp (conjugateProduct k L I G)).codRestrict
      (fixedSubgroup k L I G) (conjugateProduct_fixed k L I G))

/-- The extended norm point is exactly the product of the conjugates in the center. -/
@[simp] theorem extend_normPoint
    (x : Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I L)))) :
    extend k L I G (normPoint k L I G x) = (conjugateProduct k L I G x).val :=
  extend_descend k L I G _

/-- The descended central product remains central over the base polynomial algebra. -/
theorem normPoint_mem_center
    (x : Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I L)))) :
    normPoint k L I G x ∈
      Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I k))) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply extend_injective k L I G
  simp only [map_mul, extend_normPoint]
  exact (Subgroup.mem_center_iff.mp (conjugateProduct k L I G x).property) _

/-- The finite-Galois norm is a homomorphism between centers of actual polynomial-point groups. -/
def norm :
    Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I L))) →*
      Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I k))) :=
  (normPoint k L I G).codRestrict _ (normPoint_mem_center k L I G)

@[simp] theorem extend_norm
    (x : Subgroup.center (G.affinePoints (CommAlgCat.of k (MvPolynomial I L)))) :
    extend k L I G (norm k L I G x).val = (conjugateProduct k L I G x).val :=
  extend_normPoint k L I G x

end Langlands.GroupScheme.PolynomialPoint
