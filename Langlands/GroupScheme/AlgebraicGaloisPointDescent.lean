import Langlands.GroupScheme.GaloisPointDescent
import Mathlib.FieldTheory.Galois.Infinite

/-! # Effective affine-point descent over arbitrary Galois extensions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisPoint

open Langlands.AlgebraicGeometry.PointTopology

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
  [IsGalois k L]

/-- Fixed coefficients lie in the base field, with no finite-degree assumption. -/
theorem coordinate_mem_range_algebraic
    (x : fixedSubgroup k L G) (a : AffineCoordinateRing k G.X) :
    coordinates k G L x.val a ∈ Set.range (algebraMap k L) := by
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro σ
  simpa only [coordinates_conjugate] using
    congrArg (fun z => coordinates k G L z a) (x.property σ)

/-- The unique base-field value of a fixed coefficient. -/
def algebraicDescendValue
    (x : fixedSubgroup k L G) (a : AffineCoordinateRing k G.X) : k :=
  (coordinate_mem_range_algebraic k L G x a).choose

@[simp] theorem algebraMap_algebraicDescendValue
    (x : fixedSubgroup k L G) (a : AffineCoordinateRing k G.X) :
    algebraMap k L (algebraicDescendValue k L G x a) =
      coordinates k G L x.val a :=
  (coordinate_mem_range_algebraic k L G x a).choose_spec

/-- The descended regular-function values form an actual algebra map. -/
def algebraicDescendCoordinates (x : fixedSubgroup k L G) :
    AffineCoordinateRing k G.X →ₐ[k] k where
  toFun := algebraicDescendValue k L G x
  map_one' := (algebraMap k L).injective (by
    simp only [algebraMap_algebraicDescendValue, map_one])
  map_mul' a b := (algebraMap k L).injective (by
    simp only [map_mul, algebraMap_algebraicDescendValue])
  map_zero' := (algebraMap k L).injective (by
    simp only [algebraMap_algebraicDescendValue, map_zero])
  map_add' a b := (algebraMap k L).injective (by
    simp only [map_add, algebraMap_algebraicDescendValue])
  commutes' r := (algebraMap k L).injective (by
    change algebraMap k L
      (algebraicDescendValue k L G x (algebraMap k _ r)) = algebraMap k L r
    rw [algebraMap_algebraicDescendValue, (coordinates k G L x.val).commutes])

/-- Reconstruct an actual base-field scheme point from a fixed extension point. -/
def algebraicDescend (x : fixedSubgroup k L G) :
    G.affinePoints (CommAlgCat.of k k) :=
  (coordinates k G k).symm (algebraicDescendCoordinates k L G x)

@[simp] theorem extend_algebraicDescend (x : fixedSubgroup k L G) :
    extend k L G (algebraicDescend k L G x) = x.val := by
  apply (coordinates k G L).injective
  ext a
  rw [coordinates_extend]
  change algebraMap k L ((coordinates k G k)
    ((coordinates k G k).symm (algebraicDescendCoordinates k L G x)) a) = _
  rw [Equiv.apply_symm_apply]
  exact algebraMap_algebraicDescendValue k L G x a

/-- For any Galois extension, the actual extension image is the fixed subgroup. -/
theorem mem_range_extend_iff_algebraic
    (x : G.affinePoints (CommAlgCat.of k L)) :
    x ∈ Set.range (extend k L G) ↔ x ∈ fixedSubgroup k L G := by
  constructor
  · rintro ⟨y, rfl⟩ σ
    exact conjugate_extend k L G σ y
  · intro hx
    exact ⟨algebraicDescend k L G ⟨x, hx⟩,
      extend_algebraicDescend k L G ⟨x, hx⟩⟩

/-- Actual base points are multiplicatively equivalent to the fixed points over
an arbitrary Galois extension, including an infinite one. -/
def algebraicFixedEquiv :
    G.affinePoints (CommAlgCat.of k k) ≃* fixedSubgroup k L G where
  toFun x := ⟨extend k L G x, fun σ => conjugate_extend k L G σ x⟩
  invFun := algebraicDescend k L G
  left_inv _ := extend_injective k L G (extend_algebraicDescend k L G _)
  right_inv x := Subtype.ext (extend_algebraicDescend k L G x)
  map_mul' x y := Subtype.ext (map_mul (extend k L G) x y)

@[simp] theorem algebraicFixedEquiv_val
    (x : G.affinePoints (CommAlgCat.of k k)) :
    (algebraicFixedEquiv k L G x).val = extend k L G x := rfl

@[simp] theorem extend_algebraicFixedEquiv_symm
    (x : fixedSubgroup k L G) :
    extend k L G ((algebraicFixedEquiv k L G).symm x) = x.val :=
  extend_algebraicDescend k L G x

end Langlands.GroupScheme.GaloisPoint
