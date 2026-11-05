import Langlands.GroupScheme.GaloisPointRational
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Relative finite-Galois norms on the original coefficient points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.GaloisPoint

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Extension between two coefficient fields of the same original group scheme. -/
def relativeExtend :
    G.affinePoints (CommAlgCat.of k L) →* G.affinePoints (CommAlgCat.of k M) :=
  G.affinePointMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom k L M))

/-- The relative Galois action on the original coefficient points. -/
def relativeConjugate (σ : M ≃ₐ[L] M) :
    G.affinePoints (CommAlgCat.of k M) →* G.affinePoints (CommAlgCat.of k M) :=
  conjugate k M G (σ.restrictScalars k)

@[simp] theorem relativeConjugate_mul (σ τ : M ≃ₐ[L] M)
    (x : G.affinePoints (CommAlgCat.of k M)) :
    relativeConjugate k L M G (σ * τ) x =
      relativeConjugate k L M G σ (relativeConjugate k L M G τ x) := by
  exact conjugate_mul k M G (σ.restrictScalars k) (τ.restrictScalars k) x

/-- Relative fixed points, on the original coefficient-point group. -/
def relativeFixedSubgroup : Subgroup (G.affinePoints (CommAlgCat.of k M)) where
  carrier := {x | ∀ σ : M ≃ₐ[L] M, relativeConjugate k L M G σ x = x}
  one_mem' σ := map_one _
  mul_mem' hx hy σ := by rw [map_mul, hx σ, hy σ]
  inv_mem' hx σ := by rw [map_inv, hx σ]

variable [IsAffine G.X.left]

@[simp] theorem coordinates_relativeExtend (x : G.affinePoints (CommAlgCat.of k L))
    (a : Langlands.AlgebraicGeometry.PointTopology.AffineCoordinateRing k G.X) :
    coordinates k G M (relativeExtend k L M G x) a =
      algebraMap L M (coordinates k G L x a) := by
  rw [coordinates_apply, coordinates_apply]
  exact G.affinePointEvaluation_map
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom k L M)) x a

@[simp] theorem coordinates_relativeConjugate (σ : M ≃ₐ[L] M)
    (x : G.affinePoints (CommAlgCat.of k M))
    (a : Langlands.AlgebraicGeometry.PointTopology.AffineCoordinateRing k G.X) :
    coordinates k G M (relativeConjugate k L M G σ x) a =
      σ (coordinates k G M x a) :=
  coordinates_conjugate k M G (σ.restrictScalars k) x a

theorem relativeExtend_injective : Function.Injective (relativeExtend k L M G) := by
  intro x y h
  apply (coordinates k G L).injective
  ext a
  apply (algebraMap L M).injective
  simpa only [coordinates_relativeExtend] using
    congrArg (fun z => coordinates k G M z a) h

@[simp] theorem relativeConjugate_extend (σ : M ≃ₐ[L] M)
    (x : G.affinePoints (CommAlgCat.of k L)) :
    relativeConjugate k L M G σ (relativeExtend k L M G x) =
      relativeExtend k L M G x := by
  apply (coordinates k G M).injective
  ext a
  simp only [coordinates_relativeConjugate, coordinates_relativeExtend, AlgEquiv.commutes]

variable [FiniteDimensional L M] [IsGalois L M]

/-- Coordinates of relative fixed points lie in the intermediate coefficient field. -/
theorem relativeCoordinate_mem_range (x : relativeFixedSubgroup k L M G)
    (a : Langlands.AlgebraicGeometry.PointTopology.AffineCoordinateRing k G.X) :
    coordinates k G M x.val a ∈ Set.range (algebraMap L M) := by
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro σ
  simpa only [coordinates_relativeConjugate] using
    congrArg (fun z => coordinates k G M z a) (x.property σ)

/-- The unique intermediate-field value of a fixed coordinate. -/
def relativeDescendValue (x : relativeFixedSubgroup k L M G)
    (a : Langlands.AlgebraicGeometry.PointTopology.AffineCoordinateRing k G.X) : L :=
  (relativeCoordinate_mem_range k L M G x a).choose

@[simp] theorem algebraMap_relativeDescendValue (x : relativeFixedSubgroup k L M G)
    (a : Langlands.AlgebraicGeometry.PointTopology.AffineCoordinateRing k G.X) :
    algebraMap L M (relativeDescendValue k L M G x a) = coordinates k G M x.val a :=
  (relativeCoordinate_mem_range k L M G x a).choose_spec

/-- Descended coordinates retain their original `k`-algebra structure. -/
def relativeDescendCoordinates (x : relativeFixedSubgroup k L M G) :
    Langlands.AlgebraicGeometry.PointTopology.AffineCoordinateRing k G.X →ₐ[k] L where
  toFun := relativeDescendValue k L M G x
  map_one' := (algebraMap L M).injective (by simp only [algebraMap_relativeDescendValue, map_one])
  map_mul' a b := (algebraMap L M).injective (by
    simp only [map_mul, algebraMap_relativeDescendValue])
  map_zero' := (algebraMap L M).injective (by simp only [algebraMap_relativeDescendValue, map_zero])
  map_add' a b := (algebraMap L M).injective (by
    simp only [map_add, algebraMap_relativeDescendValue])
  commutes' r := (algebraMap L M).injective (by
    change algebraMap L M (relativeDescendValue k L M G x (algebraMap k _ r)) =
      algebraMap L M (algebraMap k L r)
    rw [algebraMap_relativeDescendValue, (coordinates k G M x.val).commutes,
      IsScalarTower.algebraMap_apply k L M])

/-- Reconstruction in the original intermediate-coefficient point carrier. -/
def relativeDescend (x : relativeFixedSubgroup k L M G) :
    G.affinePoints (CommAlgCat.of k L) :=
  (coordinates k G L).symm (relativeDescendCoordinates k L M G x)

@[simp] theorem relativeExtend_descend (x : relativeFixedSubgroup k L M G) :
    relativeExtend k L M G (relativeDescend k L M G x) = x.val := by
  apply (coordinates k G M).injective
  ext a
  rw [coordinates_relativeExtend]
  change algebraMap L M ((coordinates k G L)
    ((coordinates k G L).symm (relativeDescendCoordinates k L M G x)) a) = _
  rw [Equiv.apply_symm_apply]
  exact algebraMap_relativeDescendValue k L M G x a

/-- Effective descent for relative fixed points on the original point carriers. -/
def relativeFixedEquiv :
    G.affinePoints (CommAlgCat.of k L) ≃* relativeFixedSubgroup k L M G where
  toFun x := ⟨relativeExtend k L M G x, fun σ => relativeConjugate_extend k L M G σ x⟩
  invFun := relativeDescend k L M G
  left_inv _ := relativeExtend_injective k L M G (relativeExtend_descend k L M G _)
  right_inv x := Subtype.ext (relativeExtend_descend k L M G x)
  map_mul' x y := Subtype.ext (map_mul (relativeExtend k L M G) x y)

variable (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- The full relative Galois product in the original commutative point group. -/
def relativeConjugateProduct :
    affinePoints T.toGrp (CommAlgCat.of k M) →*
      affinePoints T.toGrp (CommAlgCat.of k M) where
  toFun x := ∏ σ : M ≃ₐ[L] M, relativeConjugate k L M T.toGrp σ x
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]

omit [IsGalois L M] [IsAffine T.X.left] in
theorem relativeConjugateProduct_fixed (x : affinePoints T.toGrp (CommAlgCat.of k M)) :
    relativeConjugateProduct k L M T x ∈ relativeFixedSubgroup k L M T.toGrp := by
  intro σ
  change relativeConjugate k L M T.toGrp σ
      (∏ τ : M ≃ₐ[L] M, relativeConjugate k L M T.toGrp τ x) =
    ∏ τ : M ≃ₐ[L] M, relativeConjugate k L M T.toGrp τ x
  rw [map_prod]
  simp only [← relativeConjugate_mul]
  exact Fintype.prod_equiv (Equiv.mulLeft σ) _ _ (fun _ => rfl)

/-- The relative norm, descended to the original intermediate-coefficient points. -/
def relativeNorm :
    affinePoints T.toGrp (CommAlgCat.of k M) →*
      affinePoints T.toGrp (CommAlgCat.of k L) :=
  (relativeFixedEquiv k L M T.toGrp).symm.toMonoidHom.comp
    ((relativeConjugateProduct k L M T).codRestrict
      (relativeFixedSubgroup k L M T.toGrp) (relativeConjugateProduct_fixed k L M T))

@[simp] theorem relativeExtend_norm (x : affinePoints T.toGrp (CommAlgCat.of k M)) :
    relativeExtend k L M T.toGrp (relativeNorm k L M T x) =
      ∏ σ : M ≃ₐ[L] M, relativeConjugate k L M T.toGrp σ x :=
  relativeExtend_descend k L M T.toGrp _

end Langlands.GroupScheme.GaloisPoint
