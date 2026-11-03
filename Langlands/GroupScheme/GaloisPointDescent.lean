import Langlands.GroupScheme.AffinePointTopology
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps
import Mathlib.FieldTheory.Galois.Basic

/-! # Effective finite-Galois descent of actual affine group-scheme points -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisPoint

open Langlands.AlgebraicGeometry.PointTopology

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The action of a coefficient automorphism on the existing coefficient points. -/
def conjugate (σ : L ≃ₐ[k] L) :
    G.affinePoints (CommAlgCat.of k L) →* G.affinePoints (CommAlgCat.of k L) :=
  G.affinePointMap (CommAlgCat.ofHom σ.toAlgHom)

@[simp] theorem conjugate_one (x : G.affinePoints (CommAlgCat.of k L)) :
    conjugate k L G 1 x = x := by
  exact Lie.affineMap_id G x

@[simp] theorem conjugate_mul (σ τ : L ≃ₐ[k] L)
    (x : G.affinePoints (CommAlgCat.of k L)) :
    conjugate k L G (σ * τ) x = conjugate k L G σ (conjugate k L G τ x) := by
  exact Lie.affineMap_comp G τ.toAlgHom σ.toAlgHom x

/-- Coefficient automorphisms give the natural multiplicative Galois action. -/
instance coefficientAction :
    MulDistribMulAction (L ≃ₐ[k] L) (G.affinePoints (CommAlgCat.of k L)) where
  smul σ x := conjugate k L G σ x
  one_smul := conjugate_one k L G
  mul_smul := conjugate_mul k L G
  smul_one σ := map_one (conjugate k L G σ)
  smul_mul σ := map_mul (conjugate k L G σ)

/-- Extension of base points uses the actual algebra map. -/
def extend : G.affinePoints (CommAlgCat.of k k) →* G.affinePoints (CommAlgCat.of k L) :=
  G.affinePointMap (CommAlgCat.ofHom (Algebra.ofId k L))

@[simp] theorem conjugate_extend (σ : L ≃ₐ[k] L)
    (x : G.affinePoints (CommAlgCat.of k k)) :
    conjugate k L G σ (extend k L G x) = extend k L G x := by
  change Lie.affineMap G σ.toAlgHom (Lie.affineMap G (Algebra.ofId k L) x) = _
  rw [← Lie.affineMap_comp]
  have h : σ.toAlgHom.comp (Algebra.ofId k L) = Algebra.ofId k L := by ext
  exact congrArg (fun f => Lie.affineMap G f x) h

/-- The fixed points form a subgroup of the actual coefficient-point group. -/
def fixedSubgroup : Subgroup (G.affinePoints (CommAlgCat.of k L)) where
  carrier := {x | ∀ σ : L ≃ₐ[k] L, conjugate k L G σ x = x}
  one_mem' σ := map_one _
  mul_mem' hx hy σ := by rw [map_mul, hx σ, hy σ]
  inv_mem' hx σ := by rw [map_inv, hx σ]

@[simp] theorem mem_fixedSubgroup (x : G.affinePoints (CommAlgCat.of k L)) :
    x ∈ fixedSubgroup k L G ↔ ∀ σ : L ≃ₐ[k] L, conjugate k L G σ x = x := Iff.rfl

variable [IsAffine G.X.left]

/-- Affine global-section coordinates on the existing point carrier. -/
def coordinates (A : Type u) [CommRing A] [Algebra k A] :
    G.affinePoints (CommAlgCat.of k A) ≃ (AffineCoordinateRing k G.X →ₐ[k] A) :=
  (affineSchemePointEquiv k G.X A).trans AlgPoint.algHomEquiv

/-- These coordinates are the existing regular-function evaluation maps. -/
@[simp] theorem coordinates_apply (A : Type u) [CommRing A] [Algebra k A]
    (x : G.affinePoints (CommAlgCat.of k A)) (a : AffineCoordinateRing k G.X) :
    coordinates k G A x a = G.affinePointEvaluation (CommAlgCat.of k A) x a := by
  let f : Spec (CommRingCat.of A) ⟶ G.X.left := x.left
  change (Spec.preimage (f ≫ G.X.left.isoSpec.hom)).hom a =
    (f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom a
  have h : Spec.preimage (f ≫ G.X.left.isoSpec.hom) =
      f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, ← Scheme.isoSpec_Spec_hom]
    exact (Scheme.isoSpec_hom_naturality f).symm
  exact congrArg (fun f => f.hom a) h

@[simp] theorem coordinates_extend (x : G.affinePoints (CommAlgCat.of k k))
    (a : AffineCoordinateRing k G.X) :
    coordinates k G L (extend k L G x) a = algebraMap k L (coordinates k G k x a) := by
  rw [coordinates_apply, coordinates_apply]
  exact G.affinePointEvaluation_map (CommAlgCat.ofHom (Algebra.ofId k L)) x a

@[simp] theorem coordinates_conjugate (σ : L ≃ₐ[k] L)
    (x : G.affinePoints (CommAlgCat.of k L)) (a : AffineCoordinateRing k G.X) :
    coordinates k G L (conjugate k L G σ x) a = σ (coordinates k G L x a) := by
  rw [coordinates_apply, coordinates_apply]
  exact G.affinePointEvaluation_map (CommAlgCat.ofHom σ.toAlgHom) x a

/-- Extension is injective because the field inclusion is injective on coordinates. -/
theorem extend_injective : Function.Injective (extend k L G) := by
  intro x y h
  apply (coordinates k G k).injective
  ext a
  apply (algebraMap k L).injective
  simpa only [coordinates_extend] using congrArg (fun z => coordinates k G L z a) h

variable [FiniteDimensional k L] [IsGalois k L]

/-- Every coordinate of a fixed point lies in the base field. -/
theorem coordinate_mem_range (x : fixedSubgroup k L G) (a : AffineCoordinateRing k G.X) :
    coordinates k G L x.val a ∈ Set.range (algebraMap k L) := by
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro σ
  simpa only [coordinates_conjugate] using
    congrArg (fun z => coordinates k G L z a) (x.property σ)

/-- A coordinate is descended using the finite-Galois fixed-field theorem. -/
def descendValue (x : fixedSubgroup k L G) (a : AffineCoordinateRing k G.X) : k :=
  (coordinate_mem_range k L G x a).choose

@[simp] theorem algebraMap_descendValue (x : fixedSubgroup k L G)
    (a : AffineCoordinateRing k G.X) :
    algebraMap k L (descendValue k L G x a) = coordinates k G L x.val a :=
  (coordinate_mem_range k L G x a).choose_spec

/-- The descended coordinate values form an algebra homomorphism. -/
def descendCoordinates (x : fixedSubgroup k L G) : AffineCoordinateRing k G.X →ₐ[k] k where
  toFun := descendValue k L G x
  map_one' := (algebraMap k L).injective (by
    simp only [algebraMap_descendValue, map_one])
  map_mul' a b := (algebraMap k L).injective (by
    simp only [map_mul, algebraMap_descendValue])
  map_zero' := (algebraMap k L).injective (by
    simp only [algebraMap_descendValue, map_zero])
  map_add' a b := (algebraMap k L).injective (by
    simp only [map_add, algebraMap_descendValue])
  commutes' r := (algebraMap k L).injective (by
    change algebraMap k L (descendValue k L G x (algebraMap k _ r)) = algebraMap k L r
    rw [algebraMap_descendValue, (coordinates k G L x.val).commutes])

/-- Effective descent reconstructs the actual base point from its coordinate map. -/
def descend (x : fixedSubgroup k L G) : G.affinePoints (CommAlgCat.of k k) :=
  (coordinates k G k).symm (descendCoordinates k L G x)

@[simp] theorem extend_descend (x : fixedSubgroup k L G) :
    extend k L G (descend k L G x) = x.val := by
  apply (coordinates k G L).injective
  ext a
  rw [coordinates_extend]
  change algebraMap k L ((coordinates k G k)
    ((coordinates k G k).symm (descendCoordinates k L G x)) a) = _
  rw [Equiv.apply_symm_apply]
  exact algebraMap_descendValue k L G x a

/-- A coefficient point comes from the base exactly when every automorphism fixes it. -/
theorem mem_range_extend_iff (x : G.affinePoints (CommAlgCat.of k L)) :
    x ∈ Set.range (extend k L G) ↔ x ∈ fixedSubgroup k L G := by
  constructor
  · rintro ⟨y, rfl⟩ σ
    exact conjugate_extend k L G σ y
  · intro hx
    exact ⟨descend k L G ⟨x, hx⟩, extend_descend k L G ⟨x, hx⟩⟩

/-- Base points are multiplicatively equivalent to the fixed subgroup. -/
def fixedEquiv : G.affinePoints (CommAlgCat.of k k) ≃* fixedSubgroup k L G where
  toFun x := ⟨extend k L G x, fun σ => conjugate_extend k L G σ x⟩
  invFun := descend k L G
  left_inv _ := extend_injective k L G (extend_descend k L G _)
  right_inv x := Subtype.ext (extend_descend k L G x)
  map_mul' x y := Subtype.ext (map_mul (extend k L G) x y)

@[simp] theorem fixedEquiv_val (x : G.affinePoints (CommAlgCat.of k k)) :
    (fixedEquiv k L G x).val = extend k L G x := rfl

@[simp] theorem extend_fixedEquiv_symm (x : fixedSubgroup k L G) :
    extend k L G ((fixedEquiv k L G).symm x) = x.val := extend_descend k L G x

end Langlands.GroupScheme.GaloisPoint
