import Langlands.GroupScheme.Lie.ScalarExtension
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Absolute.RegularCocharacterMaximal
import Mathlib.RingTheory.TensorProduct.Free

/-! # Bases and images of Lie algebras after a change of the coefficient algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (A : Type u) [CommRing A] [Algebra k A]

/-- The basis of `lieKernel G A` obtained from a basis of `lieKernel G k` by change of
coefficients. -/
def kernelBaseChangeBasis {J : Type*} (e : Module.Basis J k (Additive (lieKernel G k))) :
    Module.Basis J A (Additive (lieKernel G A)) :=
  (Algebra.TensorProduct.basis A e).map (kernelScalarExtension G A)

theorem kernelBaseChangeBasis_apply {J : Type*} (e : Module.Basis J k (Additive (lieKernel G k)))
    (i : J) :
    kernelBaseChangeBasis G A e i = lieKernelMapLinear G (Algebra.ofId k A) (e i) := by
  simp [kernelBaseChangeBasis, Algebra.TensorProduct.basis_apply, kernelScalarExtension_tmul]

omit [LocallyOfFiniteType G.X.hom] in
/-- The image under change of coefficients of the `k`-span of a set lies in the `A`-span of its
image. -/
theorem lieKernelMapLinear_mem_span_image (S : Set (Additive (lieKernel G k)))
    {x : Additive (lieKernel G k)} (hx : x ∈ Submodule.span k S) :
    lieKernelMapLinear G (Algebra.ofId k A) x ∈
      Submodule.span A (lieKernelMapLinear G (Algebra.ofId k A) '' S) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul c y _ h =>
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ h

/-- Every Lie vector over `A` is an `A`-combination of vectors coming from `k`. -/
theorem mem_span_range_lieKernelMapLinear (x : Additive (lieKernel G A)) :
    x ∈ Submodule.span A (Set.range (lieKernelMapLinear G (Algebra.ofId k A))) := by
  let e := Module.finBasis k (Additive (lieKernel G k))
  have h : x ∈ Submodule.span A (Set.range (kernelBaseChangeBasis G A e)) := by
    rw [(kernelBaseChangeBasis G A e).span_eq]
    trivial
  refine Submodule.span_mono ?_ h
  rintro _ ⟨i, rfl⟩
  exact ⟨e i, (kernelBaseChangeBasis_apply G A e i).symm⟩

variable {G} {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
  [LocallyOfFiniteType H.X.hom]

omit [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom] in
/-- Change of coefficients carries the image of a homomorphism on Lie algebras over `k` into
its image over `A`. -/
theorem lieKernelMapLinear_mem_range_targetMapLinear (f : H ⟶ G)
    {x : Additive (lieKernel G k)} (hx : x ∈ LinearMap.range (targetMapLinear f k)) :
    lieKernelMapLinear G (Algebra.ofId k A) x ∈ LinearMap.range (targetMapLinear f A) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨lieKernelMapLinear H (Algebra.ofId k A) y,
    (lieKernelMapLinear_targetMapLinear f (Algebra.ofId k A) y).symm⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- The image of a homomorphism on Lie algebras over `A` is spanned by the images over `k`
after change of coefficients. -/
theorem range_targetMapLinear_le_span (f : H ⟶ G) (S : Submodule k (Additive (lieKernel G k)))
    (hS : LinearMap.range (targetMapLinear f k) ≤ S) :
    LinearMap.range (targetMapLinear f A) ≤
      Submodule.span A (lieKernelMapLinear G (Algebra.ofId k A) '' S) := by
  rintro _ ⟨y, rfl⟩
  have hy := mem_span_range_lieKernelMapLinear H A y
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨z, rfl⟩ := hz
    rw [← lieKernelMapLinear_targetMapLinear]
    exact Submodule.subset_span ⟨_, hS ⟨z, rfl⟩, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul c y _ h => rw [map_smul]; exact Submodule.smul_mem _ c h

omit [LocallyOfFiniteType G.X.hom] in
/-- With a spanning set from a `k`-span: the `A`-image of a homomorphism lies in the `A`-span of
the changed vectors. -/
theorem range_targetMapLinear_le_span_of_le_span (f : H ⟶ G) (T : Set (Additive (lieKernel G k)))
    (hT : LinearMap.range (targetMapLinear f k) ≤ Submodule.span k T) :
    LinearMap.range (targetMapLinear f A) ≤
      Submodule.span A (lieKernelMapLinear G (Algebra.ofId k A) '' T) := by
  refine (range_targetMapLinear_le_span A f _ hT).trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact lieKernelMapLinear_mem_span_image G A T hx

end Langlands.GroupScheme.Lie
