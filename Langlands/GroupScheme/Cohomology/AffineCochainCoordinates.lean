import Langlands.GroupScheme.Cohomology.RegularCochains
import Langlands.GroupScheme.Lie.AffineCoordinates
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Coordinate-module descriptions of regular cochains on affine groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cohomology

variable {R : CommRingCat.{u}} (H : GroupScheme (Spec R)) [IsAffineHom H.X.hom]

/-- The actual universal point in a chosen affine presentation of the source. -/
def genericPoint : H.affinePoints (Lie.coordinateAlgebra H) :=
  (Lie.pointCoordinates H).symm (AlgHom.id R (Lie.coordinateAlgebra H))

@[simp]
theorem genericPoint_coordinates :
    Lie.pointCoordinates H (genericPoint H) = AlgHom.id R (Lie.coordinateAlgebra H) :=
  (Lie.pointCoordinates H).apply_symm_apply _

/-- The coefficient-algebra morphism corresponding to an actual source point. -/
def pointSpecialization {A : CommAlgCat.{u} R} (h : H.affinePoints A) :
    Lie.coordinateAlgebra H ⟶ A :=
  CommAlgCat.ofHom (Lie.pointCoordinates H h)

@[simp]
theorem pointSpecialization_generic : pointSpecialization H (genericPoint H) = 𝟙 _ := by
  change CommAlgCat.ofHom
    (Lie.pointCoordinates H ((Lie.pointCoordinates H).symm (AlgHom.id R _))) = _
  rw [Equiv.apply_symm_apply]
  rfl

@[simp]
theorem genericPoint_specialize {A : CommAlgCat.{u} R} (h : H.affinePoints A) :
    H.affinePointMap (pointSpecialization H h) (genericPoint H) = h := by
  apply (Lie.pointCoordinates H).injective
  change Lie.pointCoordinates H
    (Lie.affineMap H (Lie.pointCoordinates H h) (genericPoint H)) = _
  rw [Lie.pointCoordinates_naturality]
  erw [genericPoint_coordinates H, AlgHom.comp_id]

theorem pointSpecialization_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (h : H.affinePoints A) :
    pointSpecialization H (H.affinePointMap f h) = pointSpecialization H h ≫ f := by
  change CommAlgCat.ofHom (Lie.pointCoordinates H (Lie.affineMap H f.hom h)) = _
  rw [Lie.pointCoordinates_naturality]
  rfl

variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Specializing an element over the universal source point gives a regular
one-cochain on all affine tests. -/
def oneCochainOfCoordinates (v : ModulePoints M (Lie.coordinateAlgebra H)) :
    OneCochain M H where
  value A h := modulePointMap M (pointSpecialization H h) v
  naturality f h := by
    rw [pointSpecialization_naturality, modulePointMap_comp]
    rfl

omit [IsAffineHom H.X.hom] in
@[ext]
theorem OneCochain.ext {c d : OneCochain M H}
    (h : ∀ (A : CommAlgCat.{u} R) (x : H.affinePoints A), c.value A x = d.value A x) :
    c = d := by
  cases c with
  | mk cv cn =>
    cases d with
    | mk dv dn =>
      have hv : cv = dv := funext fun A => funext fun x => h A x
      cases hv
      rfl

/-- The universal-point description of regular one-cochains with arbitrary
module coefficients; no finiteness or projectivity is required. -/
def oneCochainCoordinateEquiv :
    OneCochain M H ≃ ModulePoints M (Lie.coordinateAlgebra H) where
  toFun c := c.value _ (genericPoint H)
  invFun := oneCochainOfCoordinates H M
  left_inv c := by
    apply OneCochain.ext
    intro A h
    simpa only [oneCochainOfCoordinates, genericPoint_specialize] using
      c.naturality (pointSpecialization H h) (genericPoint H)
  right_inv v := by
    change modulePointMap M (pointSpecialization H (genericPoint H)) v = v
    rw [pointSpecialization_generic, modulePointMap_id]
    rfl

/-- The coordinate algebra of two independent universal source points. -/
abbrev pairCoordinateAlgebra : CommAlgCat.{u} R :=
  CommAlgCat.of R (Lie.coordinateAlgebra H ⊗[R] Lie.coordinateAlgebra H)

def genericFirst : H.affinePoints (pairCoordinateAlgebra H) :=
  Lie.affineMap H (Algebra.TensorProduct.includeLeft :
    Lie.coordinateAlgebra H →ₐ[R] Lie.coordinateAlgebra H ⊗[R] Lie.coordinateAlgebra H)
      (genericPoint H)

def genericSecond : H.affinePoints (pairCoordinateAlgebra H) :=
  Lie.affineMap H (Algebra.TensorProduct.includeRight :
    Lie.coordinateAlgebra H →ₐ[R] Lie.coordinateAlgebra H ⊗[R] Lie.coordinateAlgebra H)
      (genericPoint H)

/-- Specialize the pair of independent generic points to a prescribed pair. -/
def pairSpecialization {A : CommAlgCat.{u} R} (h k : H.affinePoints A) :
    pairCoordinateAlgebra H ⟶ A :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift
    (Lie.pointCoordinates H h) (Lie.pointCoordinates H k) (fun _ _ => Commute.all _ _))

@[simp]
theorem pairSpecialization_tmul {A : CommAlgCat.{u} R} (h k : H.affinePoints A)
    (b c : Lie.coordinateAlgebra H) :
    (pairSpecialization H h k).hom (b ⊗ₜ[R] c) =
      Lie.pointCoordinates H h b * Lie.pointCoordinates H k c := rfl

@[simp]
theorem genericFirst_specialize {A : CommAlgCat.{u} R} (h k : H.affinePoints A) :
    H.affinePointMap (pairSpecialization H h k) (genericFirst H) = h := by
  change Lie.affineMap H _ (Lie.affineMap H _ (genericPoint H)) = h
  rw [← Lie.affineMap_comp]
  change Lie.affineMap H
    ((Algebra.TensorProduct.lift (Lie.pointCoordinates H h) (Lie.pointCoordinates H k)
      (fun _ _ => Commute.all _ _)).comp Algebra.TensorProduct.includeLeft)
        (genericPoint H) = h
  rw [Algebra.TensorProduct.lift_comp_includeLeft]
  exact genericPoint_specialize H h

@[simp]
theorem genericSecond_specialize {A : CommAlgCat.{u} R} (h k : H.affinePoints A) :
    H.affinePointMap (pairSpecialization H h k) (genericSecond H) = k := by
  change Lie.affineMap H _ (Lie.affineMap H _ (genericPoint H)) = k
  rw [← Lie.affineMap_comp]
  change Lie.affineMap H
    ((Algebra.TensorProduct.lift (Lie.pointCoordinates H h) (Lie.pointCoordinates H k)
      (fun _ _ => Commute.all _ _)).comp Algebra.TensorProduct.includeRight)
        (genericPoint H) = k
  rw [Algebra.TensorProduct.lift_comp_includeRight']
  exact genericPoint_specialize H k

theorem pairSpecialization_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (h k : H.affinePoints A) :
    pairSpecialization H (H.affinePointMap f h) (H.affinePointMap f k) =
      pairSpecialization H h k ≫ f := by
  apply CommAlgCat.hom_ext
  apply Algebra.TensorProduct.ext'
  intro b c
  change Lie.pointCoordinates H (Lie.affineMap H f.hom h) b *
      Lie.pointCoordinates H (Lie.affineMap H f.hom k) c =
    f.hom (Lie.pointCoordinates H h b * Lie.pointCoordinates H k c)
  rw [Lie.pointCoordinates_naturality, Lie.pointCoordinates_naturality,
    AlgHom.comp_apply, AlgHom.comp_apply, map_mul]

@[simp]
theorem pairSpecialization_generic :
    pairSpecialization H (genericFirst H) (genericSecond H) = 𝟙 _ := by
  apply CommAlgCat.hom_ext
  apply Algebra.TensorProduct.ext'
  intro b c
  change Lie.pointCoordinates H (genericFirst H) b *
      Lie.pointCoordinates H (genericSecond H) c = b ⊗ₜ[R] c
  simp only [genericFirst, genericSecond, Lie.pointCoordinates_naturality,
    AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]
  erw [genericPoint_coordinates H]
  rfl

/-- Specializing a module element over the pair-coordinate algebra gives a
regular two-cochain. -/
def twoCochainOfCoordinates (v : ModulePoints M (pairCoordinateAlgebra H)) :
    TwoCochain M H where
  value A h k := modulePointMap M (pairSpecialization H h k) v
  naturality f h k := by
    rw [pairSpecialization_naturality, modulePointMap_comp]
    rfl

omit [IsAffineHom H.X.hom] in
@[ext]
theorem TwoCochain.ext {c d : TwoCochain M H}
    (h : ∀ (A : CommAlgCat.{u} R) (x y : H.affinePoints A),
      c.value A x y = d.value A x y) : c = d := by
  cases c with
  | mk cv cn =>
    cases d with
    | mk dv dn =>
      have hv : cv = dv := funext fun A => funext fun x => funext fun y => h A x y
      cases hv
      rfl

/-- The coordinate-module description of regular two-cochains. -/
def twoCochainCoordinateEquiv :
    TwoCochain M H ≃ ModulePoints M (pairCoordinateAlgebra H) where
  toFun c := c.value _ (genericFirst H) (genericSecond H)
  invFun := twoCochainOfCoordinates H M
  left_inv c := by
    apply TwoCochain.ext
    intro A h k
    simpa only [twoCochainOfCoordinates, genericFirst_specialize,
      genericSecond_specialize] using
        c.naturality (pairSpecialization H h k) (genericFirst H) (genericSecond H)
  right_inv v := by
    change modulePointMap M
      (pairSpecialization H (genericFirst H) (genericSecond H)) v = v
    rw [pairSpecialization_generic, modulePointMap_id]
    rfl

/-- The one-cocycle equation can be checked on the independent generic pair. -/
theorem oneCocycle_iff_generic (ρ : ModuleRepresentation M H) (c : OneCochain M H) :
    c.IsCocycle ρ ↔
      c.value (pairCoordinateAlgebra H) (genericFirst H * genericSecond H) =
        c.value _ (genericFirst H) +
          ρ.action _ (genericFirst H) (c.value _ (genericSecond H)) := by
  constructor
  · intro hc
    exact hc _ _ _
  · intro hc A h k
    have he := congrArg (modulePointMap M (pairSpecialization H h k)) hc
    simpa only [map_add, c.naturality, ρ.naturality, map_mul,
      genericFirst_specialize, genericSecond_specialize] using he

/-- A prescribed base-module element is a one-cocycle coboundary primitive
if its formula holds at the universal source point. -/
theorem oneCoboundary_iff_generic (ρ : ModuleRepresentation M H) (c : OneCochain M H) :
    c.IsCoboundary ρ ↔
      ∃ m : M, c.value _ (genericPoint H) =
        ρ.action _ (genericPoint H) ((1 : Lie.coordinateAlgebra H) ⊗ₜ[R] m) -
          (1 : Lie.coordinateAlgebra H) ⊗ₜ[R] m := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, hm _ _⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, fun A h => ?_⟩
    have he := congrArg (modulePointMap M (pointSpecialization H h)) hm
    simpa only [map_sub, c.naturality, ρ.naturality, modulePointMap_tmul,
      map_one, genericPoint_specialize] using he

/-- The two-coboundary equation can be checked on the generic pair; the
primitive remains a natural one-cochain on all affine tests. -/
theorem twoCoboundary_iff_generic (ρ : ModuleRepresentation M H) (c : TwoCochain M H) :
    c.IsCoboundary ρ ↔
      ∃ b : OneCochain M H,
        c.value _ (genericFirst H) (genericSecond H) +
            b.value _ (genericFirst H * genericSecond H) =
          ρ.action _ (genericFirst H) (b.value _ (genericSecond H)) +
            b.value _ (genericFirst H) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb _ _ _⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, fun A h k => ?_⟩
    have he := congrArg (modulePointMap M (pairSpecialization H h k)) hb
    simpa only [map_add, c.naturality, b.naturality, ρ.naturality, map_mul,
      genericFirst_specialize, genericSecond_specialize] using he

end Langlands.GroupScheme.Cohomology
