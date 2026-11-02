import Langlands.CommutativeAlgebra.ValuationFiniteFreePresentation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.Operations

/-! # Split kernels and finite homogeneous relation spaces over valuation domains -/

universe u v w

namespace Langlands.CommutativeAlgebra

open Module

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]

private theorem nonempty_kernelProjection (f : M →ₗ[R] N) :
    ∃ p : M →ₗ[R] M, LinearMap.range p = LinearMap.ker f ∧
      ∀ x ∈ LinearMap.ker f, p x = x := by
  have : Module.Free R (LinearMap.range f) :=
    free_of_finite_of_isTorsionFree_of_valuationRing (LinearMap.range f)
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let p : M →ₗ[R] M := LinearMap.id - s.comp f.rangeRestrict
  have hzero (x : M) : f (p x) = 0 := by
    have h := congrArg (fun y : LinearMap.range f => (y : N)) (DFunLike.congr_fun hs (f.rangeRestrict x))
    change f (x - s (f.rangeRestrict x)) = 0
    rw [map_sub]
    exact sub_eq_zero.2 h.symm
  have hid (x : M) (hx : x ∈ LinearMap.ker f) : p x = x := by
    have hx' : f.rangeRestrict x = 0 := Subtype.ext hx
    simp [p, hx']
  refine ⟨p, ?_, hid⟩
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact hzero x
  · intro x hx
    exact ⟨x, hid x hx⟩

/-- A chosen projection onto the actual kernel of a map from a finite module
 to a torsion-free module over a valuation domain. -/
noncomputable def valuationKernelProjection (f : M →ₗ[R] N) : M →ₗ[R] M :=
  Classical.choose (nonempty_kernelProjection f)

theorem valuationKernelProjection_range (f : M →ₗ[R] N) :
    LinearMap.range (valuationKernelProjection f) = LinearMap.ker f :=
  (Classical.choose_spec (nonempty_kernelProjection f)).1

theorem valuationKernelProjection_apply (f : M →ₗ[R] N) (x : M)
    (hx : x ∈ LinearMap.ker f) : valuationKernelProjection f x = x :=
  (Classical.choose_spec (nonempty_kernelProjection f)).2 x hx

theorem valuationKernelProjection_idempotent (f : M →ₗ[R] N) :
    (valuationKernelProjection f).comp (valuationKernelProjection f) =
      valuationKernelProjection f := by
  ext x
  apply valuationKernelProjection_apply
  rw [← valuationKernelProjection_range f]
  exact LinearMap.mem_range_self _ _

/-- Kernels of maps from finite modules to torsion-free modules over a valuation domain are finite. -/
theorem finite_kernel_of_valuationRing (f : M →ₗ[R] N) :
    Module.Finite R (LinearMap.ker f) := by
  rw [← valuationKernelProjection_range f]
  infer_instance

/-- A torsion-free finite source also makes its kernel free. -/
theorem free_kernel_of_valuationRing [Module.IsTorsionFree R M] (f : M →ₗ[R] N) :
    Module.Free R (LinearMap.ker f) := by
  have := finite_kernel_of_valuationRing f
  exact free_of_finite_of_isTorsionFree_of_valuationRing (LinearMap.ker f)

/-- Intersecting the kernel with an ideal multiple of the source gives the same ideal multiple
 of the kernel. -/
theorem kernel_inf_ideal_smul_of_valuationRing (f : M →ₗ[R] N) (I : Ideal R) :
    LinearMap.ker f ⊓ I • (⊤ : Submodule R M) = I • LinearMap.ker f := by
  apply le_antisymm
  · intro x hx
    have hm : valuationKernelProjection f x ∈
        (I • (⊤ : Submodule R M)).map (valuationKernelProjection f) :=
      Submodule.mem_map_of_mem hx.2
    simpa only [Submodule.map_smul'', Submodule.map_top,
      valuationKernelProjection_range, valuationKernelProjection_apply f x hx.1] using hm
  · exact le_inf Submodule.smul_le_right (smul_mono_right I le_top)

variable {σ : Type*} [Finite σ]

/-- Vectors whose polynomial coordinates are homogeneous of the specified degree. -/
noncomputable def homogeneousPolynomialVectors (R : Type u) [CommRing R] (σ : Type*)
    (n d : ℕ) :
    Submodule R (Fin n → MvPolynomial σ R) :=
  Submodule.pi Set.univ fun _ => MvPolynomial.homogeneousSubmodule σ R d

omit [IsDomain R] [ValuationRing R] in
theorem homogeneousPolynomialVectors_finite (n d : ℕ) :
    Module.Finite R (homogeneousPolynomialVectors R σ n d) := by
  apply Module.Finite.of_fg
  exact Submodule.fg_pi fun _ => MvPolynomial.homogeneousSubmodule_fg σ R d

/-- The actual kernel on the finite space of homogeneous polynomial vectors. -/
noncomputable def homogeneousPolynomialKernelPiece {n m : ℕ}
    (f : (Fin n → MvPolynomial σ R) →ₗ[MvPolynomial σ R] (Fin m → MvPolynomial σ R))
    (d : ℕ) : Submodule R (homogeneousPolynomialVectors R σ n d) :=
  LinearMap.ker ((f.restrictScalars R).comp (homogeneousPolynomialVectors R σ n d).subtype)

theorem homogeneousPolynomialKernelPiece_finite {n m : ℕ}
    (f : (Fin n → MvPolynomial σ R) →ₗ[MvPolynomial σ R] (Fin m → MvPolynomial σ R))
    (d : ℕ) : Module.Finite R (homogeneousPolynomialKernelPiece f d) := by
  have := homogeneousPolynomialVectors_finite (R := R) (σ := σ) n d
  exact finite_kernel_of_valuationRing _

theorem homogeneousPolynomialKernelPiece_free {n m : ℕ}
    (f : (Fin n → MvPolynomial σ R) →ₗ[MvPolynomial σ R] (Fin m → MvPolynomial σ R))
    (d : ℕ) : Module.Free R (homogeneousPolynomialKernelPiece f d) := by
  have := homogeneousPolynomialKernelPiece_finite f d
  exact free_of_finite_of_isTorsionFree_of_valuationRing (homogeneousPolynomialKernelPiece f d)

end Langlands.CommutativeAlgebra
