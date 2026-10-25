import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Polynomial.Roots

/-! Integral operators give finite spectral support for covariant bilinear forms. -/

noncomputable section

open scoped TensorProduct
open Polynomial

namespace Langlands

universe uV uW

variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The tensor product of endomorphism algebras acts on the tensor product of carriers. -/
def tensorEndAction :
    (Module.End ℂ V) ⊗[ℂ] (Module.End ℂ W) →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] W) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (TensorProduct.homTensorHomMap (RingHom.id ℂ) V W V W)
    (by intros; exact TensorProduct.map_mul _ _ _ _)
    (by exact TensorProduct.map_one)

/-- The tensor product of two integral operators is integral, even on infinite-dimensional
carriers. -/
theorem isIntegral_tensorMap (A : Module.End ℂ V) (B : Module.End ℂ W)
    (hA : IsIntegral ℂ A) (hB : IsIntegral ℂ B) :
    IsIntegral ℂ (TensorProduct.map A B) := by
  let S := Algebra.adjoin ℂ ({A} : Set (Module.End ℂ V))
  let T := Algebra.adjoin ℂ ({B} : Set (Module.End ℂ W))
  let : Module.Finite ℂ S := Algebra.finite_adjoin_simple_of_isIntegral hA
  let : Module.Finite ℂ T := Algebra.finite_adjoin_simple_of_isIntegral hB
  let a : S := ⟨A, Algebra.self_mem_adjoin_singleton ℂ A⟩
  let b : T := ⟨B, Algebra.self_mem_adjoin_singleton ℂ B⟩
  let f := tensorEndAction.comp (Algebra.TensorProduct.map S.val T.val)
  exact (IsIntegral.of_finite ℂ (a ⊗ₜ[ℂ] b)).map f

/-- A functional intertwining an operator with scalar multiplication also intertwines
all polynomials in that operator. -/
theorem functional_aeval (A : Module.End ℂ V) (L : V →ₗ[ℂ] ℂ) (c : ℂ)
    (h : ∀ v, L (A v) = c * L v) (p : ℂ[X]) (v : V) :
    L (aeval A p v) = p.eval c * L v := by
  induction p using Polynomial.induction_on with
  | C a => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial n a ih =>
    rw [mul_comm, pow_succ', mul_assoc, map_mul, Module.End.mul_apply, aeval_X, h,
      mul_comm (X ^ n) (C a), ih]
    simp [mul_assoc]

/-- One finite set controls all scalars and all covariant bilinear forms. -/
theorem exists_finite_bilinear_spectral_support
    (A : Module.End ℂ V) (B : Module.End ℂ W)
    (hA : IsIntegral ℂ A) (hB : IsIntegral ℂ B) :
    ∃ E : Finset ℂ, ∀ c : ℂ, c ∉ E →
      ∀ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ,
        (∀ v w, β (A v) (B w) = c * β v w) → β = 0 := by
  classical
  obtain ⟨p, hp, hpAB⟩ := isIntegral_tensorMap A B hA hB
  change aeval (TensorProduct.map A B) p = 0 at hpAB
  refine ⟨p.roots.toFinset, ?_⟩
  intro c hc β hβ
  have hpc : p.eval c ≠ 0 := by
    intro hzero
    exact hc (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp.ne_zero).mpr hzero))
  let L := TensorProduct.lift β
  have hL : ∀ x, L (TensorProduct.map A B x) = c * L x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul v w => exact hβ v w
    | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  ext v w
  have hz := functional_aeval (TensorProduct.map A B) L c hL p (v ⊗ₜ[ℂ] w)
  rw [hpAB] at hz
  have : p.eval c * β v w = 0 := by simpa [L] using hz.symm
  exact (mul_eq_zero.mp this).resolve_left hpc

/-- Pull a finite exceptional set back through a positive integral power. -/
def powerSpectralExceptions (E : Finset ℂ) (m : ℕ) : Finset ℂ :=
  E.biUnion fun c => (X ^ m - C c : ℂ[X]).roots.toFinset

theorem pow_not_mem_of_not_mem_powerSpectralExceptions
    (E : Finset ℂ) (m : ℕ) (hm : 0 < m) (z : ℂ)
    (hz : z ∉ powerSpectralExceptions E m) : z ^ m ∉ E := by
  intro hpow
  apply hz
  apply Finset.mem_biUnion.mpr
  refine ⟨z ^ m, hpow, Multiset.mem_toFinset.mpr ?_⟩
  apply (Polynomial.mem_roots (X_pow_sub_C_ne_zero hm (z ^ m))).mpr
  simp [Polynomial.IsRoot]

/-- The same finite-support assertion when the covariance scalar is a fixed
positive integral power of the parameter. -/
theorem exists_finite_bilinear_power_spectral_support
    (A : Module.End ℂ V) (B : Module.End ℂ W)
    (hA : IsIntegral ℂ A) (hB : IsIntegral ℂ B) (m : ℕ) (hm : 0 < m) :
    ∃ E : Finset ℂ, ∀ z : ℂ, z ∉ E →
      ∀ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ,
        (∀ v w, β (A v) (B w) = z ^ m * β v w) → β = 0 := by
  obtain ⟨E, hE⟩ := exists_finite_bilinear_spectral_support A B hA hB
  exact ⟨powerSpectralExceptions E m, fun z hz =>
    hE (z ^ m) (pow_not_mem_of_not_mem_powerSpectralExceptions E m hm z hz)⟩

end Langlands
