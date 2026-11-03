import Langlands.GroupScheme.SubgroupFunctor
import Langlands.GroupScheme.Lie.KernelTargetMaps

/-! # Tangent submodules of actual subgroup functors -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
variable (F : SubgroupFunctor G) (A : Type u) [CommRing A] [Algebra R A]
variable [IsAffineHom G.X.hom]

/-- The tangent submodule consists of actual dual-number identity points
which belong to the subgroup functor. -/
def lie : Submodule A (Additive (lieKernel G A)) where
  carrier := {x | x.toMul.val ∈ F.carrier ((algSpec R).obj
    (op (CommAlgCat.of R (DualNumber A))))}
  zero_mem' := (F.carrier _).one_mem
  add_mem' hx hy := (F.carrier _).mul_mem hx hy
  smul_mem' c _x hx := F.comp_mem ((algSpec R).map
    (CommAlgCat.ofHom (GeneralLinear.DualNumber.epsilonScaleAlg (R := R) c)).op) hx

@[simp] theorem mem_lie {x : Additive (lieKernel G A)} :
    x ∈ F.lie A ↔ x.toMul.val ∈ F.carrier
      ((algSpec R).obj (op (CommAlgCat.of R (DualNumber A)))) := Iff.rfl

/-- Inclusion on every test scheme induces inclusion of tangent submodules. -/
theorem lie_mono {F F' : SubgroupFunctor G} (h : F ≤ F') :
    F.lie A ≤ F'.lie A := fun _ hx => h _ hx

/-- Coefficient extension preserves the tangent points of any subgroup functor. -/
theorem lie_map_mem {B : Type u} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) {x : Additive (lieKernel G A)} (hx : x ∈ F.lie A) :
    lieKernelMapLinear G f x ∈ F.lie B :=
  F.comp_mem ((algSpec R).map
    (CommAlgCat.ofHom (GeneralLinear.DualNumber.coefficientAlgMap f)).op) hx

/-- The tangent submodule of a represented subgroup is the range of its
actual linear map on identity kernels. -/
theorem lie_eq_range [IsAffineHom H.X.hom] (i : H ⟶ G)
    (hrep : F.IsRepresentedBy i) :
    F.lie A = LinearMap.range (Lie.targetMapLinear i A) := by
  have : Mono i.hom.hom := hrep.1
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    rw [mem_lie, ← hrep.2] at hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hx
    have hred : Lie.reduction G (y ≫ i.hom.hom) = 1 := by
      rw [hy]
      exact x.toMul.property
    refine ⟨Additive.ofMul ⟨y, mem_lieKernel_of_comp i y hred⟩, ?_⟩
    apply Additive.toMul.injective
    exact Subtype.ext hy
  · rintro ⟨y, rfl⟩
    rw [mem_lie, ← hrep.2]
    exact SubgroupFunctor.mem_range.2 ⟨y.toMul.val, rfl⟩

end Langlands.GroupScheme.SubgroupFunctor
