import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Unramified.Pi

/-!
# Group-likes from algebra homomorphisms out of the convolution dual

For a finite-dimensional coalgebra `D` over a field `k`, every `k`-algebra homomorphism
from the convolution dual `WithConv (D →ₗ[k] k)` to `k` is evaluation at a group-like
element of `D`. Consequently, when such homomorphisms separate the points of the
convolution dual (for example when it is a finite product of copies of `k`, or when it
is commutative and formally unramified over a separably closed `k`), the group-like
elements of `D` span `D`. Formal unramifiedness descends from a split scalar extension
`K ⊗[k] A ≃ₐ[K] (ι → K)` along any field extension `K / k`.
-/

open scoped TensorProduct
open Coalgebra TensorProduct WithConv

namespace Langlands.CoalgebraDescent

variable {k : Type*} [Field k] {D : Type*} [AddCommGroup D] [Module k D]

/-- Two elements of `D ⊗ D` agree once all functionals `φ ⊗ ψ` agree on them. -/
theorem tensor_eq_of_forall_dual [FiniteDimensional k D] {t t' : D ⊗[k] D}
    (h : ∀ φ ψ : Module.Dual k D,
      LinearMap.mul' k k (TensorProduct.map φ ψ t) = LinearMap.mul' k k (TensorProduct.map φ ψ t')) :
    t = t' := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff k (t - t')).mp fun θ => ?_
  obtain ⟨x, rfl⟩ := (dualDistribEquiv k D D).surjective θ
  induction x using TensorProduct.inductionOn with
  | tmul φ ψ =>
    have hφψ : (dualDistribEquiv k D D (φ ⊗ₜ ψ) : D ⊗[k] D →ₗ[k] k) =
        LinearMap.mul' k k ∘ₗ TensorProduct.map φ ψ := by
      ext m n
      simp [mul_comm]
    rw [hφψ, map_sub, LinearMap.comp_apply, LinearMap.comp_apply, h, sub_self]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, add_zero]

variable [Coalgebra k D]

/-- Every `k`-algebra homomorphism from the convolution dual of a finite-dimensional
coalgebra `D` to `k` is evaluation at a group-like element of `D`. -/
theorem exists_isGroupLikeElem_of_algHom [FiniteDimensional k D]
    (χ : WithConv (D →ₗ[k] k) →ₐ[k] k) :
    ∃ d : D, IsGroupLikeElem k d ∧ ∀ φ : D →ₗ[k] k, χ (toConv φ) = φ d := by
  let ℓ : Module.Dual k (Module.Dual k D) :=
    χ.toLinearMap ∘ₗ (WithConv.linearEquiv k (D →ₗ[k] k)).symm.toLinearMap
  let d : D := (Module.evalEquiv k D).symm ℓ
  have hd : ∀ φ : D →ₗ[k] k, χ (toConv φ) = φ d := fun φ => by
    rw [Module.apply_evalEquiv_symm_apply]
    rfl
  refine ⟨d, ⟨?_, ?_⟩, hd⟩
  · have h1 : (1 : WithConv (D →ₗ[k] k)) = toConv (counit (R := k) (A := D)) := by
      rw [LinearMap.convOne_def]
      congr 1
    rw [← hd, ← h1, map_one]
  · refine tensor_eq_of_forall_dual fun φ ψ => ?_
    have := map_mul χ (toConv φ) (toConv ψ)
    rw [hd, hd, ← toConv_ofConv (toConv φ * toConv ψ), hd, LinearMap.convMul_apply] at this
    simpa using this

/-- If the `k`-algebra homomorphisms from the convolution dual of a finite-dimensional
coalgebra `D` to `k` separate its points, then the group-like elements span `D`. -/
theorem span_isGroupLikeElem_eq_top_of_algHom_separating [FiniteDimensional k D]
    (hsep : ∀ x : WithConv (D →ₗ[k] k),
      (∀ χ : WithConv (D →ₗ[k] k) →ₐ[k] k, χ x = 0) → x = 0) :
    Submodule.span k {d : D | IsGroupLikeElem k d} = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr hne) inferInstance
  refine hφ (toConv_eq_zero.mp (hsep (toConv φ) fun χ => ?_))
  obtain ⟨d, hd, hχ⟩ := exists_isGroupLikeElem_of_algHom χ
  rw [hχ, ← Submodule.mem_bot k, ← hmap]
  exact Submodule.mem_map_of_mem (Submodule.subset_span hd)

/-- If the convolution dual of a finite-dimensional coalgebra `D` is isomorphic, as a
`k`-algebra, to a product of copies of `k`, then the group-like elements span `D`. -/
theorem span_isGroupLikeElem_eq_top_of_algEquiv_pi [FiniteDimensional k D] {ι : Type*}
    (e : WithConv (D →ₗ[k] k) ≃ₐ[k] (ι → k)) :
    Submodule.span k {d : D | IsGroupLikeElem k d} = ⊤ := by
  refine span_isGroupLikeElem_eq_top_of_algHom_separating fun x hx => ?_
  refine e.injective ?_
  ext i
  simpa using hx ((Pi.evalAlgHom k (fun _ : ι => k) i).comp e.toAlgHom)

/-- Over a separably closed field, if a finite-dimensional cocommutative coalgebra `D`
has formally unramified convolution dual, then the group-like elements span `D`. -/
theorem span_isGroupLikeElem_eq_top_of_formallyUnramified [IsSepClosed k]
    [FiniteDimensional k D] [Coalgebra.IsCocomm k D]
    [Algebra.FormallyUnramified k (WithConv (D →ₗ[k] k))] :
    Submodule.span k {d : D | IsGroupLikeElem k d} = ⊤ := by
  have : Module.Finite k (WithConv (D →ₗ[k] k)) :=
    Module.Finite.equiv (WithConv.linearEquiv k (D →ₗ[k] k)).symm
  have : Algebra.FormallyEtale k (WithConv (D →ₗ[k] k)) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field k _
  exact span_isGroupLikeElem_eq_top_of_algEquiv_pi
    (Algebra.FormallyEtale.equivPiOfIsSepClosed k (WithConv (D →ₗ[k] k)))

omit [Coalgebra k D] in
/-- A commutative `k`-algebra whose scalar extension to some field `K` is a finite
product of copies of `K` is formally unramified over `k`. -/
theorem formallyUnramified_of_tensorProduct_algEquiv_pi {A : Type*} [CommRing A]
    [Algebra k A] (K : Type*) [Field K] [Algebra k K] {ι : Type*} [Finite ι]
    (e : K ⊗[k] A ≃ₐ[K] (ι → K)) :
    Algebra.FormallyUnramified k A := by
  have : Algebra.FormallyUnramified K (K ⊗[k] A) := .of_equiv e.symm
  exact .of_formallyUnramified_tensorProduct_of_faithfullyFlat K

/-- Over a separably closed field `k`, if a finite-dimensional cocommutative coalgebra `D`
has a convolution dual whose scalar extension to some field `K` is a finite product of
copies of `K`, then the group-like elements span `D`. -/
theorem span_isGroupLikeElem_eq_top_of_tensorProduct_algEquiv_pi [IsSepClosed k]
    [FiniteDimensional k D] [Coalgebra.IsCocomm k D] (K : Type*) [Field K] [Algebra k K]
    {ι : Type*} [Finite ι] (e : K ⊗[k] WithConv (D →ₗ[k] k) ≃ₐ[K] (ι → K)) :
    Submodule.span k {d : D | IsGroupLikeElem k d} = ⊤ := by
  have := formallyUnramified_of_tensorProduct_algEquiv_pi K e
  exact span_isGroupLikeElem_eq_top_of_formallyUnramified

end Langlands.CoalgebraDescent
