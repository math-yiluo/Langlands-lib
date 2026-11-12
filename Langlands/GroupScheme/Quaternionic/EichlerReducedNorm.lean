import Langlands.GroupScheme.Quaternionic.HyperbolicLevi
import Langlands.Algebra.QuaternionCommutator

/-!
# Levi elements of square reduced norm lie in the Eichler subgroup

Let `D` be a quaternion division algebra over `K` (reduced degree `2`) with an involution of
the first kind `σ`, and let `(e, f)` be a hyperbolic pair of a `σ`-quadratic form `q` such
that some `x₀ ⊥ e, f` has `q(x₀) ≠ 0` and `σ` has a nonzero alternating element `a₀`. Then every
unit `a` of reduced norm `1`, and more generally of reduced norm a square in `K`, lies in
`N_E = {a | ℓ(a) ∈ E}`: the hyperbolic scaling `ℓ(a)` is a product of Eichler
transformations.

The proof writes `a = y X y⁻¹ X⁻¹` with `X = z + s`, `z = -σ(c₀) a₀⁻¹` (`[c₀] = q(x₀)`), by
`CentralDivision.exists_mul_add_eq_conj`, and recognizes `X = σ(c) σ(a₀)⁻¹` for
`c = c₀ + s a₀`, so that `commutator_mem_eichlerLeviSubgroup` applies.
-/

noncomputable section

universe u w

open Matrix Langlands.CentralSimple
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution.Eichler

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] {σ : FirstKindInvolution K D} {n : Type w} [Fintype n]
  [DecidableEq n] [LinearOrder n] {q : σ.QuadraticForms n}

/-- Units of reduced norm `1` lie in `N_E`. -/
theorem mem_eichlerLeviSubgroup_of_reducedNorm_eq_one (hd : reducedDegree K D = 2)
    {e f x0 : n → D} {a0 : D} (hP : IsHyperbolic σ q e f)
    (ha0 : a0 ∈ σ.alternatingSubspace) (ha00 : a0 ≠ 0)
    (hx0e : σ.sesqForm (σ.polar q) x0 e = 0) (hx0f : σ.sesqForm (σ.polar q) x0 f = 0)
    (hx0 : σ.quadraticValue x0 q ≠ 0) (a : Dˣ)
    (ha : reducedNorm K D K (1 ⊗ₜ[K] (a : D)) = 1) : a ∈ eichlerLeviSubgroup hP := by
  obtain ⟨c0, hc0⟩ := Submodule.Quotient.mk_surjective _ (σ.quadraticValue x0 q)
  have hσa0 : σ a0 = -a0 := map_eq_neg_of_mem_alternatingSubspace σ ha0
  have hσa00 : σ a0 ≠ 0 := map_ne_zero_of_ne_zero σ ha00
  obtain ⟨z, hz⟩ : ∃ z : D, z = -(σ c0 * a0⁻¹) := ⟨_, rfl⟩
  have hzK : z ∉ Set.range (algebraMap K D) := by
    rintro ⟨k, hk⟩
    apply hx0
    rw [← hc0, Submodule.Quotient.mk_eq_zero]
    have h1 : σ c0 = -(algebraMap K D k * a0) := by
      rw [hk, hz, neg_mul, neg_neg, mul_assoc, inv_mul_cancel₀ ha00, mul_one]
    have h2 : c0 = k • a0 := by
      rw [← apply_apply σ c0, h1, map_neg, map_mul, map_algebraMap, hσa0, neg_mul, neg_neg,
        Algebra.smul_def, Algebra.commutes]
    rw [h2]
    exact Submodule.smul_mem _ _ ha0
  obtain ⟨s, y, hy⟩ := CentralDivision.exists_mul_add_eq_conj K D hd hzK ha
  obtain ⟨X, hX⟩ : ∃ X : D, X = z + algebraMap K D s := ⟨_, rfl⟩
  rw [← hX] at hy
  have hX0 : X ≠ 0 := by
    intro h
    apply hzK
    refine ⟨-s, ?_⟩
    rw [_root_.map_neg]
    exact (eq_neg_of_add_eq_zero_left (hX ▸ h)).symm
  obtain ⟨c, hcdef⟩ : ∃ c : D, c = c0 + s • a0 := ⟨_, rfl⟩
  have hc : (Submodule.Quotient.mk c : D ⧸ σ.alternatingSubspace) = σ.quadraticValue x0 q := by
    rw [hcdef, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2
      (Submodule.smul_mem _ _ ha0), add_zero, hc0]
  have hcne : c ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [← hc, Submodule.Quotient.mk_zero])
  have hW : σ c = X * σ a0 := by
    rw [hcdef, map_add, map_smul, hσa0, hX, hz, Algebra.smul_def]
    simp only [add_mul, neg_mul, mul_neg, mul_assoc, inv_mul_cancel₀ ha00, mul_one]
    abel
  set W : Dˣ := Units.mk0 (σ c) (map_ne_zero_of_ne_zero σ hcne)
  set W0 : Dˣ := Units.mk0 (σ a0) hσa00
  have hWW0 : W * W0⁻¹ = Units.mk0 X hX0 := by
    ext
    simp only [W, W0, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, hW,
      mul_inv_cancel_right₀ hσa00]
  have key := commutator_mem_eichlerLeviSubgroup hP hx0e hx0f hcne hc ha0 ha00 W W0 rfl rfl y⁻¹
  rw [hWW0, inv_inv] at key
  convert key using 1
  ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [← Units.val_inv_eq_inv_val, ← hy, mul_inv_cancel_right₀ hX0]

/-- Units whose reduced norm is a square in `K` lie in `N_E`. -/
theorem mem_eichlerLeviSubgroup_of_reducedNorm_eq_sq (hd : reducedDegree K D = 2)
    {e f x0 : n → D} {a0 : D} (hP : IsHyperbolic σ q e f)
    (ha0 : a0 ∈ σ.alternatingSubspace) (ha00 : a0 ≠ 0)
    (hx0e : σ.sesqForm (σ.polar q) x0 e = 0) (hx0f : σ.sesqForm (σ.polar q) x0 f = 0)
    (hx0 : σ.quadraticValue x0 q ≠ 0) (a : Dˣ) (t : K)
    (ha : reducedNorm K D K (1 ⊗ₜ[K] (a : D)) = t ^ 2) : a ∈ eichlerLeviSubgroup hP := by
  have hunit : IsUnit ((1 : K) ⊗ₜ[K] (a : D)) :=
    ⟨⟨1 ⊗ₜ[K] (a : D), 1 ⊗ₜ[K] ((a⁻¹ : Dˣ) : D),
      by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Units.mul_inv,
        Algebra.TensorProduct.one_def],
      by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Units.inv_mul,
        Algebra.TensorProduct.one_def]⟩, rfl⟩
  have ht : t ≠ 0 := by
    rintro rfl
    have := hunit.map (reducedNorm K D K)
    rw [ha] at this
    simp at this
  have hT0 : algebraMap K D t ≠ 0 := by simpa using ht
  set T : Dˣ := Units.mk0 (algebraMap K D t) hT0
  have hTmem : T ∈ eichlerLeviSubgroup hP := algebraMap_mem_eichlerLeviSubgroup hP ha0 ha00 ht T rfl
  have hb : reducedNorm K D K (1 ⊗ₜ[K] ((T⁻¹ * a : Dˣ) : D)) = 1 := by
    have h1 : (1 : K) ⊗ₜ[K] ((T⁻¹ * a : Dˣ) : D) = (t⁻¹ ⊗ₜ[K] (1 : D)) * (1 ⊗ₜ[K] (a : D)) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← map_inv₀,
        ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.TensorProduct.tmul_mul_tmul, smul_eq_mul, mul_one, one_mul]
    rw [h1, _root_.map_mul, reducedNorm_scalar, hd, ha, ← mul_pow, inv_mul_cancel₀ ht, one_pow]
  have hbmem := mem_eichlerLeviSubgroup_of_reducedNorm_eq_one hd hP ha0 ha00 hx0e hx0f hx0 _ hb
  have : a = T * (T⁻¹ * a) := by group
  rw [this]
  exact mul_mem hTmem hbmem

end FirstKindInvolution.Eichler

end Langlands.GroupScheme.Quaternionic
