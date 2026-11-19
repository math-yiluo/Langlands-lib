import Langlands.Representation.Archimedean.RealBlockLeftDerivative
import Langlands.Representation.Archimedean.RealSphericalKrylov

/-!
# One Lie step on quadratic functions of the compact group

Let `φ` be a smooth function on `GL_N(ℝ)` that transforms on the left under the upper triangular
Borel subgroup by the exponents `α`. On `O(N)` the right derivative of `φ` splits into an upper
triangular part, given by `α`, and rotation parts, which only see `φ` on `O(N)`.

If `G_0, …, G_{N-1}` are such functions with `G_c(κ) = ∑_l p_l κ_{lc} κ_{lb}` on `O(N)`, then
`∑_c R(E_{ac}) G_c (κ) = ∑_l (S p)_l κ_{la} κ_{lb}` on `O(N)`, where `S = sOp s` is the operator of
`RealSphericalKrylov` with `s_l = α_l + l`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

namespace RealSphericalStep

open RealPrincipalSeriesDuality RealBlockDerivative RealSphericalKrylov

variable {N : ℕ}

/-! ## The decomposition of a right derivative on `O(N)` -/

/-- On `O(N)`, the right derivative of an exponent-equivariant smooth function is the upper
triangular part `(∑ᵢ αᵢ Sᵢᵢ) φ(k)` plus the rotation parts `S_{ba} dφ_k(W_{ab} k)` for `a < b`,
where `S = k X kᵀ` and `W_{ab} = E_{ba} - E_{ab}`. -/
theorem rightDerivative_eq_decomp {α : Fin N → ℂ} {φ : Langlands.GeneralLinear N ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) (hα : IsExpEquivariant α φ)
    (X : Matrix (Fin N) (Fin N) ℝ) (k : unitaryCompact ℝ N) :
    rightDerivative (matrixModel ℝ N) X φ (k : Langlands.GeneralLinear N ℝ) =
      (∑ i, α i * ((conjT X ((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)
        i i : ℝ) : ℂ)) * φ k +
      ∑ a, ∑ b, if a < b then
        ((conjT X ((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) b a : ℝ) : ℂ) *
          fderiv ℝ (unitsExtension φ) ((k : Langlands.GeneralLinear N ℝ) :
            Matrix (Fin N) (Fin N) ℝ)
            (rotGen a b * ((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ))
        else 0 := by
  set km : Matrix (Fin N) (Fin N) ℝ := ((k : Langlands.GeneralLinear N ℝ) :
    Matrix (Fin N) (Fin N) ℝ) with hkm
  set S := conjT X km with hS
  set L := fderiv ℝ (unitsExtension φ) km with hL
  set R : Matrix (Fin N) (Fin N) ℝ := ∑ a, ∑ b, if a < b then S b a • rotGen a b else 0
    with hR
  have h1 : rightDerivative (matrixModel ℝ N) X φ (k : Langlands.GeneralLinear N ℝ) =
      L (km * X) := rightDerivative_eq_fderiv hφ X _
  have h2 : km * X = (S - R) * km + R * km := by
    rw [sub_mul, sub_add_cancel, hS, conjT, mul_assoc, transpose_mul_self_of_mem k, mul_one]
  have hU : L ((S - R) * km) = (∑ i, α i * (S i i : ℂ)) * φ k := by
    have h := fderiv_upperTriangular_of_isExpEquivariant hφ hα (k : Langlands.GeneralLinear N ℝ)
      (isUpperTriangular_sub_rotSum S)
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_rotSum_apply_self]
  have hRk : R * km = ∑ a, ∑ b, if a < b then S b a • (rotGen a b * km) else 0 := by
    rw [hR, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [smul_mul_assoc]
    · rw [zero_mul]
  have hLR : L (R * km) = ∑ a, ∑ b, if a < b then (S b a : ℂ) * L (rotGen a b * km) else 0 := by
    rw [hRk, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [map_smul, Complex.real_smul]
    · rw [map_zero]
  rw [h1, h2, map_add, hU, hLR]

/-! ## Rotation derivatives of functions given on `O(N)` -/

/-- If `φ = g` on `O(N)`, the derivative of `φ` at `k ∈ O(N)` along the rotation direction
`W k` is the derivative of `g` along the curve `t ↦ exp(tW) k`. -/
theorem fderiv_rot_eq {φ : Langlands.GeneralLinear N ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) (k : unitaryCompact ℝ N)
    {g : Matrix (Fin N) (Fin N) ℝ → ℂ}
    (hφg : ∀ κ : unitaryCompact ℝ N, φ (κ : Langlands.GeneralLinear N ℝ) =
      g ((κ : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ))
    (W : Matrix (Fin N) (Fin N) ℝ) (hW : W ∈ skewAdjoint (Matrix (Fin N) (Fin N) ℝ)) {g' : ℂ}
    (hg : HasDerivAt (fun t : ℝ => g (NormedSpace.exp (t • W) *
      ((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ))) g' 0) :
    fderiv ℝ (unitsExtension φ) ((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)
      (W * ((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)) = g' := by
  set km : Matrix (Fin N) (Fin N) ℝ := ((k : Langlands.GeneralLinear N ℝ) :
    Matrix (Fin N) (Fin N) ℝ) with hkm
  have hcurve : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • W) * km) (W * km) 0 :=
    (hasDerivAt_exp_smul_zero W).mul_const km
  have hψ : HasFDerivAt (unitsExtension φ) (fderiv ℝ (unitsExtension φ) km)
      (NormedSpace.exp ((0 : ℝ) • W) * km) := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]
    exact (differentiableAt_unitsExtension hφ (Units.isUnit _)).hasFDerivAt
  have hB : HasDerivAt (fun t : ℝ => unitsExtension φ (NormedSpace.exp (t • W) * km))
      (fderiv ℝ (unitsExtension φ) km (W * km)) 0 :=
    by
      have h := hψ.comp_hasDerivAt (0 : ℝ) hcurve
      exact h
  have heq : (fun t : ℝ => unitsExtension φ (NormedSpace.exp (t • W) * km)) =
      fun t : ℝ => g (NormedSpace.exp (t • W) * km) := by
    funext t
    have hval : NormedSpace.exp (t • W) * km =
        (((expK W hW t * k : unitaryCompact ℝ N) : Langlands.GeneralLinear N ℝ) :
          Matrix (Fin N) (Fin N) ℝ) := rfl
    rw [hval, unitsExtension_val]
    exact hφg _
  rw [heq] at hB
  exact hB.unique hg

/-- The quadratic function `M ↦ ∑_l p_l M_{lc} M_{lb}`. -/
def quad (p : Fin N → ℂ) (c b : Fin N) (M : Matrix (Fin N) (Fin N) ℝ) : ℂ :=
  ∑ l, p l * ((M l c : ℝ) : ℂ) * ((M l b : ℝ) : ℂ)

/-- The derivative of `quad` along `t ↦ exp(tW) M`. -/
theorem hasDerivAt_quad (p : Fin N → ℂ) (c b : Fin N) (W M : Matrix (Fin N) (Fin N) ℝ) :
    HasDerivAt (fun t : ℝ => quad p c b (NormedSpace.exp (t • W) * M))
      (∑ l, p l * ((((W * M) l c : ℝ) : ℂ) * ((M l b : ℝ) : ℂ) +
        ((M l c : ℝ) : ℂ) * (((W * M) l b : ℝ) : ℂ))) 0 := by
  have hcurve : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • W) * M) (W * M) 0 :=
    (hasDerivAt_exp_smul_zero W).mul_const M
  have he : ∀ i j : Fin N, HasDerivAt
      (fun t : ℝ => (((NormedSpace.exp (t • W) * M) i j : ℝ) : ℂ)) (((W * M) i j : ℝ) : ℂ) 0 :=
    fun i j => (hasDerivAt_entry hcurve i j).ofReal_comp
  have h0 : NormedSpace.exp ((0 : ℝ) • W) * M = M := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]
  unfold quad
  refine (HasDerivAt.fun_sum fun l _ => ((he l c).const_mul (p l)).mul (he l b)).congr_deriv ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [h0]
  ring

/-- `(E_{ji} M)_{lc} = δ_{lj} M_{ic}`. -/
theorem single_mul_apply_eq (i j l c : Fin N) (M : Matrix (Fin N) (Fin N) ℝ) :
    (Matrix.single j i (1 : ℝ) * M) l c = if l = j then M i c else 0 := by
  by_cases h : l = j
  · subst h
    simp
  · simp [Matrix.single_mul_apply_of_ne _ _ _ _ _ h, h]

/-- The derivative of `quad p c b` along the rotation `W_{ij} = E_{ji} - E_{ij}` at `M`. -/
theorem quad_rot (p : Fin N → ℂ) (c b : Fin N) (M : Matrix (Fin N) (Fin N) ℝ) {i j : Fin N}
    (hij : i ≠ j) :
    (∑ l, p l * ((((rotGen i j * M) l c : ℝ) : ℂ) * ((M l b : ℝ) : ℂ) +
        ((M l c : ℝ) : ℂ) * (((rotGen i j * M) l b : ℝ) : ℂ))) =
      (p j - p i) * (((M i c : ℝ) : ℂ) * ((M j b : ℝ) : ℂ) +
        ((M j c : ℝ) : ℂ) * ((M i b : ℝ) : ℂ)) := by
  have hrot : ∀ l d : Fin N, (rotGen i j * M) l d =
      (if l = j then M i d else 0) - (if l = i then M j d else 0) := by
    intro l d
    rw [rotGen, Matrix.sub_mul, Matrix.sub_apply, single_mul_apply_eq, single_mul_apply_eq]
  simp only [hrot]
  have hsplit : ∀ l : Fin N, p l * ((((if l = j then M i c else 0) - (if l = i then M j c else 0) :
      ℝ) : ℂ) * ((M l b : ℝ) : ℂ) + ((M l c : ℝ) : ℂ) *
      (((if l = j then M i b else 0) - (if l = i then M j b else 0) : ℝ) : ℂ)) =
      (if l = j then p j * (((M i c : ℝ) : ℂ) * ((M j b : ℝ) : ℂ) +
          ((M j c : ℝ) : ℂ) * ((M i b : ℝ) : ℂ)) else 0) -
        (if l = i then p i * (((M j c : ℝ) : ℂ) * ((M i b : ℝ) : ℂ) +
          ((M i c : ℝ) : ℂ) * ((M j b : ℝ) : ℂ)) else 0) := by
    intro l
    by_cases hlj : l = j
    · subst hlj
      simp only [ite_true, ite_eq_right hij.symm]
      push_cast
      ring
    · by_cases hli : l = i
      · subst hli
        simp only [ite_true, ite_eq_right hlj]
        push_cast
        ring
      · simp only [ite_eq_right hlj, ite_eq_right hli]
        push_cast
        ring
  simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-! ## The algebraic identity -/

/-- Rows of an orthogonal matrix are orthonormal, in complex form. -/
theorem sum_mul_eq_of_mem (k : unitaryCompact ℝ N) (i j : Fin N) :
    (∑ c, ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) i c : ℝ) : ℂ) *
      ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) j c : ℝ) : ℂ)) =
      if i = j then 1 else 0 := by
  have h2 : ((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) *
      (((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ))ᵀ = 1 :=
    mul_transpose_self_of_mem k
  have h4 := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i j) h2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h4
  rw [← Complex.ofReal_inj] at h4
  push_cast at h4
  rw [h4]
  split_ifs <;> simp

/-- The number of `i : Fin N` with `i < l` is `l`. -/
theorem sum_lt_const (l : Fin N) (z : ℂ) : (∑ i : Fin N, if i < l then z else 0) = (l : ℕ) * z := by
  rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul]

/-- The algebraic identity behind the step formula. -/
theorem step_algebra (k : unitaryCompact ℝ N) (α p : Fin N → ℂ) (a b : Fin N) :
    (∑ c, ((∑ i, α i * (((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) i a :
        ℝ) : ℂ) * ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) i c : ℝ) : ℂ))) *
        (∑ l, p l * ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) l c :
          ℝ) : ℂ) * ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) l b :
          ℝ) : ℂ)) +
      ∑ i, ∑ j, if i < j then
        (((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) j a : ℝ) : ℂ) *
          ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) i c : ℝ) : ℂ)) *
        ((p j - p i) *
          (((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) i c : ℝ) : ℂ) *
            ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) j b : ℝ) : ℂ) +
          ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) j c : ℝ) : ℂ) *
            ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) i b : ℝ) : ℂ)))
        else 0)) =
      ∑ l, sOp (fun l => α l + ((l : ℕ) : ℂ)) p l *
        ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) l a : ℝ) : ℂ) *
        ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) l b : ℝ) : ℂ) := by
  set K : Fin N → Fin N → ℂ := fun i j =>
    ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) i j : ℝ) : ℂ) with hKdef
  have horth : ∀ i j, (∑ c, K i c * K j c) = if i = j then 1 else 0 := sum_mul_eq_of_mem k
  change (∑ c, ((∑ i, α i * (K i a * K i c)) * (∑ l, p l * K l c * K l b) +
      ∑ i, ∑ j, if i < j then (K j a * K i c) * ((p j - p i) * (K i c * K j b + K j c * K i b))
        else 0)) = ∑ l, sOp (fun l => α l + ((l : ℕ) : ℂ)) p l * K l a * K l b
  have hP1 : (∑ c, (∑ i, α i * (K i a * K i c)) * (∑ l, p l * K l c * K l b)) =
      ∑ i, α i * p i * K i a * K i b := by
    calc (∑ c, (∑ i, α i * (K i a * K i c)) * (∑ l, p l * K l c * K l b))
        = ∑ c, ∑ i, ∑ l, α i * K i a * p l * K l b * (K i c * K l c) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
          ring
      _ = ∑ i, ∑ l, α i * K i a * p l * K l b * ∑ c, K i c * K l c := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, α i * p i * K i a * K i b := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
            ite_true]
          ring
  have hP2 : (∑ c, ∑ i, ∑ j, if i < j then (K j a * K i c) *
        ((p j - p i) * (K i c * K j b + K j c * K i b)) else 0) =
      ∑ i, ∑ j, if i < j then K j a * (p j - p i) * K j b else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i < j
    · simp only [ite_eq_left hij]
      have hne : i ≠ j := ne_of_lt hij
      calc (∑ c, K j a * K i c * ((p j - p i) * (K i c * K j b + K j c * K i b)))
          = K j a * (p j - p i) * (K j b * ∑ c, K i c * K i c + K i b * ∑ c, K i c * K j c) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
            refine Finset.sum_congr rfl fun c _ => ?_
            ring
        _ = K j a * (p j - p i) * K j b := by
            rw [horth, horth, ite_eq_left rfl, ite_eq_right hne]
            ring
    · simp only [ite_eq_right hij, Finset.sum_const_zero]
  have hP2' : (∑ i, ∑ j, if i < j then K j a * (p j - p i) * K j b else 0) =
      ∑ l : Fin N, (((l : ℕ) : ℂ) * p l - ∑ i : Fin N, if i < l then p i else 0) * K l a * K l b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h1 : (∑ i, if i < l then K l a * (p l - p i) * K l b else 0) =
        K l a * K l b * ∑ i, if i < l then (p l - p i) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    have h2 : (∑ i : Fin N, if i < l then (p l - p i) else 0) =
        (∑ i : Fin N, if i < l then p l else 0) - ∑ i : Fin N, if i < l then p i else 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    rw [h1, h2, sum_lt_const]
    ring
  rw [Finset.sum_add_distrib, hP1, hP2, hP2', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sOp_apply]
  ring

/-! ## The step formula -/

/-- The entries of `k E_{ac} kᵀ`. -/
theorem conjT_single_apply (M : Matrix (Fin N) (Fin N) ℝ) (a c x y : Fin N) :
    conjT (Matrix.single a c (1 : ℝ)) M x y = M x a * M y c := by
  rw [conjT, Matrix.mul_apply, Finset.sum_eq_single c]
  · rw [Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [Matrix.single_apply_same, mul_one]
    · intro j _ hj
      rw [Matrix.single_apply_of_row_ne hj.symm, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · intro j _ hj
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro i _
    rw [Matrix.single_apply_of_col_ne _ _ hj.symm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- **The step formula.** Let `G_0, …, G_{N-1}` be smooth functions on `GL_N(ℝ)` that are
exponent-equivariant for the same `α`, with `G_c(κ) = ∑_l p_l κ_{lc} κ_{lb}` on `O(N)`. Then on
`O(N)`, `∑_c R(E_{ac}) G_c (k) = ∑_l (S p)_l k_{la} k_{lb}`, where `S = sOp s` with
`s_l = α_l + l`. -/
theorem sum_rightDerivative_single {α : Fin N → ℂ} {G : Fin N → Langlands.GeneralLinear N ℝ → ℂ}
    (hG : ∀ c, ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ (G c))
    (hα : ∀ c, IsExpEquivariant α (G c)) (p : Fin N → ℂ) (b : Fin N)
    (hGK : ∀ c, ∀ κ : unitaryCompact ℝ N, G c (κ : Langlands.GeneralLinear N ℝ) =
      quad p c b ((κ : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ))
    (a : Fin N) (k : unitaryCompact ℝ N) :
    (∑ c, rightDerivative (matrixModel ℝ N) (Matrix.single a c (1 : ℝ)) (G c)
      (k : Langlands.GeneralLinear N ℝ)) =
      ∑ l, sOp (fun l => α l + ((l : ℕ) : ℂ)) p l *
        ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) l a : ℝ) : ℂ) *
        ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) l b : ℝ) : ℂ) := by
  set km : Matrix (Fin N) (Fin N) ℝ := ((k : Langlands.GeneralLinear N ℝ) :
    Matrix (Fin N) (Fin N) ℝ) with hkm
  rw [← step_algebra k α p a b]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [rightDerivative_eq_decomp (hG c) (hα c), hGK c k]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjT_single_apply]
    push_cast
    ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · rw [fderiv_rot_eq (hG c) k (hGK c) (rotGen i j) (rotGen_mem_skewAdjoint i j)
        (hasDerivAt_quad p c b (rotGen i j) km), quad_rot p c b km (ne_of_lt hij),
        conjT_single_apply]
      push_cast
      ring
    · rfl

end RealSphericalStep

end Langlands.Archimedean
