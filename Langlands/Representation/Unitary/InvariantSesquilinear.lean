import Langlands.LinearAlgebra.LocallyFiniteHermitian
import Langlands.Representation.Unitary.ConjugateSpace
import Langlands.Representation.Unitary.Restriction
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.Tactic.LinearCombination

/-! # Algebraic invariant sesquilinear forms and finite tensor products -/

noncomputable section

open scoped ComplexConjugate

namespace Langlands.InvariantSesquilinear

universe uG uI uV

section Single

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A complex sesquilinear form is detected by its diagonal. -/
theorem eq_zero_of_diagonal (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hb : ∀ x, b x x = 0) : b = 0 := by
  ext x y
  have h₁ := hb (x + y)
  have h₂ := hb (x + Complex.I • y)
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply, Complex.conj_I, hb, zero_add,
    add_zero, mul_zero] at h₁ h₂
  change b x y = 0
  linear_combination (norm := (ring_nf; simp [Complex.I_sq]))
    (1 / 2 : ℂ) * h₁ - (Complex.I / 2) * h₂

/-- Every nonzero complex sesquilinear form has a nonzero diagonal value. -/
theorem exists_diagonal_ne_zero (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hb : b ≠ 0) :
    ∃ x, b x x ≠ 0 := by
  by_contra! h
  exact hb (eq_zero_of_diagonal b h)

variable {G : Type uG} [Group G] (ρ : Representation ℂ G V)

/-- The radical of a nonzero invariant form on an irreducible representation
vanishes. Hermitian symmetry is unnecessary. -/
theorem nondegenerate_of_irreducible
    (hi : Representation.IsIrreducible ρ) (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hb : b ≠ 0) (hinv : ∀ g x y, b (ρ g x) (ρ g y) = b x y) :
    ∀ x : V, (∀ y, b x y = 0) → x = 0 := by
  let _ := hi
  let R : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker b
      apply_mem_toSubmodule := by
        intro g x hx
        change b (ρ g x) = 0
        ext y
        have h := hinv g x (ρ g⁻¹ y)
        rw [ρ.self_inv_apply] at h
        change b (ρ g x) y = 0
        rw [h]
        exact congrArg (fun f : V →ₗ[ℂ] ℂ => f (ρ g⁻¹ y)) hx }
  have hR : R ≠ ⊤ := by
    intro h
    apply hb
    ext x y
    have hx : x ∈ R := h.symm ▸ (show x ∈ (⊤ : Subrepresentation ρ) from trivial)
    exact congrArg (fun f : V →ₗ[ℂ] ℂ => f y) hx
  have hbot : R = ⊥ := (eq_bot_or_eq_top R).resolve_right hR
  intro x hx
  have hxR : x ∈ R := by
    change b x = 0
    ext y
    exact hx y
  rw [hbot] at hxR
  exact hxR

/-- Symmetric and skew-symmetric parts supply a nonzero invariant Hermitian
form from any nonzero invariant sesquilinear form. -/
theorem exists_nonzero_hermitian
    (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hb : b ≠ 0)
    (hinv : ∀ g x y, b (ρ g x) (ρ g y) = b x y) :
    ∃ H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, H ≠ 0 ∧
      (∀ x y, H y x = conj (H x y)) ∧
      ∀ g x y, H (ρ g x) (ρ g y) = H x y := by
  let a := LinearAlgebra.adjointPairing b
  have ha (x y : V) : a x y = conj (b y x) := rfl
  by_cases hs : b + a = 0
  · refine ⟨Complex.I • (b - a), ?_, ?_, ?_⟩
    · intro hzero
      apply hb
      ext x y
      have hp := congrArg (fun f : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ => f x y) hs
      have hm := congrArg (fun f : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ => f x y) hzero
      change b x y + a x y = 0 at hp
      change Complex.I * (b x y - a x y) = 0 at hm
      have hm' := (mul_eq_zero.mp hm).resolve_left Complex.I_ne_zero
      change b x y = 0
      linear_combination (1 / 2 : ℂ) * hp + (1 / 2 : ℂ) * hm'
    · intro x y
      change Complex.I * (b y x - a y x) = conj (Complex.I * (b x y - a x y))
      simp only [ha, map_mul, map_sub, Complex.conj_I, Complex.conj_conj]
      ring
    · intro g x y
      change Complex.I * (b (ρ g x) (ρ g y) - a (ρ g x) (ρ g y)) =
        Complex.I * (b x y - a x y)
      rw [hinv, ha, ha, hinv]
  · refine ⟨b + a, hs, ?_, ?_⟩
    · intro x y
      change b y x + a y x = conj (b x y + a x y)
      simp only [ha, map_add, Complex.conj_conj]
      exact add_comm _ _
    · intro g x y
      change b (ρ g x) (ρ g y) + a (ρ g x) (ρ g y) = b x y + a x y
      rw [hinv, ha, ha, hinv]

end Single

section Tensor

variable {ι : Type uI} [Fintype ι]
  {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Tensor the factor pairings, using the canonical map from the tensor of the
duals to the dual of the tensor. No finite-dimensionality is needed. -/
def tensor (b : ∀ i, V i →ₗ⋆[ℂ] V i →ₗ[ℂ] ℂ) :
    PiTensorProduct ℂ V →ₗ⋆[ℂ] PiTensorProduct ℂ V →ₗ[ℂ] ℂ :=
  PiTensorProduct.dualDistrib.comp (tensorConj b)

@[simp]
theorem tensor_tprod (b : ∀ i, V i →ₗ⋆[ℂ] V i →ₗ[ℂ] ℂ)
    (v w : ∀ i, V i) :
    tensor b (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ w) =
      ∏ i, b i (v i) (w i) := by
  simp [tensor]

/-- Two sesquilinear forms on a finite tensor product agree if they agree
on pairs of pure tensors. -/
theorem ext_tprod
    (b c : PiTensorProduct ℂ V →ₗ⋆[ℂ] PiTensorProduct ℂ V →ₗ[ℂ] ℂ)
    (h : ∀ v w, b (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ w) =
      c (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ w)) : b = c := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod d w => simp [h]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz =>
    simp only [map_add, LinearMap.add_apply, hx, hz]

/-- The tensor of Hermitian forms is Hermitian. -/
theorem tensor_hermitian (b : ∀ i, V i →ₗ⋆[ℂ] V i →ₗ[ℂ] ℂ)
    (hb : ∀ i x y, b i y x = conj (b i x y))
    (x y : PiTensorProduct ℂ V) : tensor b y x = conj (tensor b x y) := by
  have heq : tensor b = LinearAlgebra.adjointPairing (tensor b) := by
    apply ext_tprod
    intro v w
    simp only [tensor_tprod, LinearAlgebra.adjointPairing_apply, map_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [hb]
  have h := congrArg (fun f : PiTensorProduct ℂ V →ₗ⋆[ℂ]
    PiTensorProduct ℂ V →ₗ[ℂ] ℂ => f y x) heq
  exact h

/-- Nonzero factor forms give a nonzero tensor form, also for an empty
family of factors. -/
theorem tensor_ne_zero (b : ∀ i, V i →ₗ⋆[ℂ] V i →ₗ[ℂ] ℂ)
    (hb : ∀ i, b i ≠ 0) : tensor b ≠ 0 := by
  classical
  choose v hv using fun i => exists_diagonal_ne_zero (b i) (hb i)
  intro hzero
  have h := congrArg (fun f : PiTensorProduct ℂ V →ₗ⋆[ℂ]
    PiTensorProduct ℂ V →ₗ[ℂ] ℂ =>
      f (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)) hzero
  simp only [tensor_tprod, LinearMap.zero_apply] at h
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hv i)) h

variable {H : ι → Type uG} [∀ i, Group (H i)]

/-- Invariant factor pairings give an invariant pairing on the actual
external tensor representation. -/
theorem tensor_invariant (ρ : ∀ i, Representation ℂ (H i) (V i))
    (b : ∀ i, V i →ₗ⋆[ℂ] V i →ₗ[ℂ] ℂ)
    (hb : ∀ i g x y, b i (ρ i g x) (ρ i g y) = b i x y)
    (g : ∀ i, H i) (x y : PiTensorProduct ℂ V) :
    tensor b (FiniteTensor.external ρ g x) (FiniteTensor.external ρ g y) =
      tensor b x y := by
  let A := FiniteTensor.external ρ g
  have heq : ((tensor b).compl₂ A).comp A = tensor b := by
    apply ext_tprod
    intro v w
    change tensor b (FiniteTensor.external ρ g (PiTensorProduct.tprod ℂ v))
      (FiniteTensor.external ρ g (PiTensorProduct.tprod ℂ w)) = _
    simp only [FiniteTensor.external_tprod, tensor_tprod, hb]
  exact congrArg (fun f : PiTensorProduct ℂ V →ₗ⋆[ℂ]
    PiTensorProduct ℂ V →ₗ[ℂ] ℂ => f x y) heq

/-- If an external tensor product is unitarizable, each irreducible factor
carrying a nonzero sesquilinear form is unitarizable. -/
theorem factors_unitarizable_of_external
    (ρ : ∀ i, Representation ℂ (H i) (V i))
    (b : ∀ i, V i →ₗ⋆[ℂ] V i →ₗ[ℂ] ℂ)
    (hb : ∀ i, b i ≠ 0) (hi : ∀ i, Representation.IsIrreducible (ρ i))
    (hu : IsUnitarizable (FiniteTensor.external ρ)) :
    ∀ i, IsUnitarizable (ρ i) := by
  classical
  choose v hv using fun i => exists_diagonal_ne_zero (b i) (hb i)
  have htv : PiTensorProduct.tprod ℂ v ≠ 0 := by
    intro hzero
    have hp : tensor b (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) ≠ 0 := by
      rw [tensor_tprod]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hv i
    exact hp (by rw [hzero]; simp)
  intro i
  let _ := hi i
  let φ : H i →* ∀ j, H j := MonoidHom.mulSingle H i
  let A : V i →ₗ[ℂ] PiTensorProduct ℂ V := (PiTensorProduct.tprod ℂ).toLinearMap v i
  let f : (ρ i).IntertwiningMap ((FiniteTensor.external ρ).comp φ) :=
    { toLinearMap := A
      isIntertwining' := by
        intro g
        ext x
        change PiTensorProduct.tprod ℂ (Function.update v i (ρ i g x)) =
          FiniteTensor.external ρ (Pi.mulSingle i g)
            (PiTensorProduct.tprod ℂ (Function.update v i x))
        rw [FiniteTensor.external_tprod]
        congr 1
        funext j
        by_cases hj : j = i
        · subst j
          simp
        · simp [Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj] }
  have hf : f ≠ 0 := by
    intro hzero
    apply htv
    have h := congrArg (fun e : (ρ i).IntertwiningMap
      ((FiniteTensor.external ρ).comp φ) => e (v i)) hzero
    simpa [f, A, MultilinearMap.toLinearMap_apply] using h
  exact IsUnitarizable.of_injective (hu.comp φ) f
    ((Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf)

end Tensor

end Langlands.InvariantSesquilinear
