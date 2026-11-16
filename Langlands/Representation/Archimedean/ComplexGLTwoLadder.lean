import Langlands.Representation.Archimedean.ComplexGLTwoHighestWeight

/-!
# Lowering the highest weight in the `GL_2(ℂ)` principal series

Let `φ_b(z) = (1 + |z|²)^(-(q + 1 + b)) z̄^b`, `m = l_0 - l_1`, `p = q + m` and `D = 2b - m`.
For `b ≥ 1`, in the noncompact picture

`D (D + 1) (D + 2) ∂̄φ_b - β X₋φ_b + (D / 2) X₋² P φ_b = b (b - m) (b - p) (D + 2) φ_(b-1)`

with `β = -b (b - p) (D + 2) - (b + 1 - m) (q + b + 1) D` (`ncpL_ladder`). All terms are
computed from the derivatives of `(1 + |z|²)^(-γ) z^a z̄^c / (1 + |z|²)^k` (`hasWirt_mono`).
Hence a `(𝔤, K)`-submodule containing a vector with noncompact picture `φ_b` contains one
with noncompact picture `φ_(b-1)` whenever `b ≠ m`, `b ≠ p` and `D ≠ -2`
(`exists_phiB_pred_mem`).
-/

noncomputable section

open scoped TensorProduct Matrix

open Complex ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace ComplexGLTwoNoncompact

/-! ## Monomials -/

/-- `(1 + |z|²)^(-g) z^a z̄^c / (1 + |z|²)^k`. -/
def mono (g : ℂ) (k a c : ℕ) (z : ℂ) : ℂ := pw (-g) z * z ^ a * conj z ^ c / W z ^ k

theorem hasWirt_W_pow_inv (k : ℕ) (z : ℂ) :
    HasWirt (fun x => (W x ^ k)⁻¹) (-(k : ℂ) * conj z / W z ^ (k + 1))
      (-(k : ℂ) * z / W z ^ (k + 1)) z := by
  have hW := W_ne_zero z
  have h := (hasWirt_W z).zpow hW (-(k : ℤ))
  have hfun : (fun x => W x ^ (-(k : ℤ))) = fun x => (W x ^ k)⁻¹ := by
    funext x
    rw [zpow_neg, zpow_natCast]
  rw [hfun] at h
  have he : W z ^ (-(k : ℤ) - 1) = (W z ^ (k + 1))⁻¹ := by
    rw [show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  refine h.congr ?_ ?_
  · rw [he]
    push_cast
    ring
  · rw [he]
    push_cast
    ring

theorem hasWirt_mono (g : ℂ) (k a c : ℕ) (z : ℂ) :
    HasWirt (mono g k a c)
      (pw (-g) z * ((a : ℂ) * z ^ (a - 1) * conj z ^ c / W z ^ k -
        (g + k) * z ^ a * conj z ^ (c + 1) / W z ^ (k + 1)))
      (pw (-g) z * ((c : ℂ) * z ^ a * conj z ^ (c - 1) / W z ^ k -
        (g + k) * z ^ (a + 1) * conj z ^ c / W z ^ (k + 1))) z := by
  have hW := W_ne_zero z
  have h := (((hasWirt_pw (-g) z).mul ((hasWirt_id z).pow a)).mul
    ((hasWirt_conj z).pow c)).mul (hasWirt_W_pow_inv k z)
  have hfun : (fun x => pw (-g) x * x ^ a * conj x ^ c * (W x ^ k)⁻¹) = mono g k a c := by
    funext x
    rw [mono, div_eq_mul_inv]
  rw [hfun] at h
  refine h.congr ?_ ?_
  · rw [pw_sub_one, pow_succ]
    ring
  · rw [pw_sub_one, pow_succ]
    ring

/-! ## The operators on functions with known derivatives -/

variable {d : Fin 2 → ComplexCharacterData}

theorem ncpL_eXm_eq {w : Xd d} {f A B : ℂ → ℂ} (hw : ncpL d w = f)
    (hf : ∀ z, HasWirt f (A z) (B z) z) :
    ncpL d (πd d eXm w) = fun z => -(z ^ 2 * A z + (pp d + 1) * z * f z) - B z := by
  funext z
  rw [ncpL_eXm, hw, (hf z).dz_eq, (hf z).dzb_eq]

theorem ncpL_eP_eq {w : Xd d} {f A B : ℂ → ℂ} (hw : ncpL d w = f)
    (hf : ∀ z, HasWirt f (A z) (B z) z) :
    ncpL d (πd d eP w) = fun z => A z - (conj z ^ 2 * B z + (qq d + 1) * conj z * f z) := by
  funext z
  rw [ncpL_eP, hw, (hf z).dz_eq, (hf z).dzb_eq]

theorem ncpL_eDb_eq {w : Xd d} {f A B : ℂ → ℂ} (hw : ncpL d w = f)
    (hf : ∀ z, HasWirt f (A z) (B z) z) :
    ncpL d (πd d eDb w) = B := by
  funext z
  rw [ncpL_eDb, hw, (hf z).dzb_eq]

/-! ## The ladder identity -/

variable (d) in
/-- `m = l_0 - l_1`. -/
def mC : ℂ := (((d 0).weight - (d 1).weight : ℤ) : ℂ)

variable (d) in
/-- `D = 2 b - m` for `b = n + 1`. -/
def lD (n : ℕ) : ℂ := 2 * ((n : ℂ) + 1) - mC d

theorem pp_eq : pp d = qq d + mC d := by
  unfold pp qq mC
  ring

/-- The lowering identity in the noncompact picture. -/
theorem ncpL_ladder {v : Xd d} {n : ℕ} (hv : ncpL d v = phiB d (n + 1)) :
    ncpL d ((lD d n * (lD d n + 1) * (lD d n + 2)) • πd d eDb v -
        (-((n : ℂ) + 1) * ((n : ℂ) + 1 - pp d) * (lD d n + 2) -
          ((n : ℂ) + 2 - mC d) * (qq d + (n : ℂ) + 2) * lD d n) • πd d eXm v +
        (lD d n / 2) • πd d eXm (πd d eXm (πd d eP v))) =
      (((n : ℂ) + 1) * ((n : ℂ) + 1 - mC d) * ((n : ℂ) + 1 - pp d) * (lD d n + 2)) •
        phiB d n := by
  set γ : ℂ := qq d + 1 + ((n + 1 : ℕ) : ℂ) with hγ
  have hv' : ncpL d v = mono γ 0 0 (n + 1) := by
    rw [hv]
    funext z
    simp [phiB, mono, hγ]
  have hP := ncpL_eP_eq hv' (hasWirt_mono γ 0 0 (n + 1))
  have hP' : ncpL d (πd d eP v) = fun z => (-2 * γ) * mono γ 1 0 (n + 2) z := by
    rw [hP]
    funext z
    have hW := W_ne_zero z
    simp only [mono, Nat.cast_zero, zero_mul, zero_sub, pow_zero, Nat.zero_sub,
      add_zero, mul_one, pow_one, div_one, zero_add]
    unfold W at hW ⊢
    rw [hγ]
    push_cast
    field_simp
    ring
  set c1 : ℂ := -2 * γ * (γ + 1) with hc1
  set c2 : ℂ := 2 * γ * (pp d + 1) with hc2
  set c3 : ℂ := 2 * γ * ((n : ℂ) + 2) with hc3
  have hX1 := ncpL_eXm_eq hP' (fun z => (hasWirt_mono γ 1 0 (n + 2) z).const_mul (-2 * γ))
  have hX1' : ncpL d (πd d eXm (πd d eP v)) = fun z =>
      c1 * mono γ 2 2 (n + 3) z + c2 * mono γ 1 1 (n + 2) z + c3 * mono γ 1 0 (n + 1) z +
        c1 * mono γ 2 1 (n + 2) z := by
    rw [hX1]
    funext z
    have hW := W_ne_zero z
    have e1 : n + 2 - 1 = n + 1 := rfl
    simp only [mono, e1, Nat.cast_zero, zero_mul, pow_zero, Nat.zero_sub, mul_one, pow_one,
      zero_add]
    unfold W at hW ⊢
    rw [hc1, hc2, hc3]
    push_cast
    field_simp
    ring
  have hX2 := ncpL_eXm_eq hX1' (fun z =>
    ((((hasWirt_mono γ 2 2 (n + 3) z).const_mul c1).add
      ((hasWirt_mono γ 1 1 (n + 2) z).const_mul c2)).add
      ((hasWirt_mono γ 1 0 (n + 1) z).const_mul c3)).add
      ((hasWirt_mono γ 2 1 (n + 2) z).const_mul c1))
  have hXv := ncpL_eXm_eq hv' (hasWirt_mono γ 0 0 (n + 1))
  have hDv := ncpL_eDb_eq hv' (hasWirt_mono γ 0 0 (n + 1))
  have hphi : ∀ z, phiB d n z = pw (-γ) z * W z * conj z ^ n := by
    intro z
    have e : -(qq d + 1 + (n : ℂ)) = -γ + 1 := by
      rw [hγ]
      push_cast
      ring
    rw [phiB, e, pw_add_one]
  rw [map_add, map_sub, map_smul, map_smul, map_smul, hX2, hXv, hDv]
  funext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hphi]
  have hW := W_ne_zero z
  have e1 : n + 1 - 1 = n := rfl
  have e2 : n + 2 - 1 = n + 1 := rfl
  have e3 : n + 3 - 1 = n + 2 := rfl
  simp only [mono, e1, e2, e3, Nat.cast_zero, zero_mul, zero_sub, pow_zero, Nat.zero_sub,
    add_zero, mul_one, pow_one, div_one, zero_add, Nat.add_one_sub_one]
  generalize pw (-γ) z = P
  rw [pp_eq] at hc2
  rw [hc1, hc2, hc3, hγ]
  unfold lD
  rw [pp_eq]
  unfold W at hW ⊢
  push_cast
  field_simp
  ring

/-- A `(𝔤, K)`-submodule containing a vector with noncompact picture `φ_(n+1)` contains one with
noncompact picture `φ_n`, unless the coefficient of `φ_n` in the ladder identity vanishes. -/
theorem exists_phiB_pred_mem (S : Submodule ℂ (Xd d))
    (hS : IsGKSubmodule (complexStandardRep 2 (List.ofFn d)) (πd d) S) {v : Xd d} (hvS : v ∈ S)
    {n : ℕ} (hv : ncpL d v = phiB d (n + 1))
    (hc : ((n : ℂ) + 1) * ((n : ℂ) + 1 - mC d) * ((n : ℂ) + 1 - pp d) * (lD d n + 2) ≠ 0) :
    ∃ w ∈ S, ncpL d w = phiB d n := by
  have hu : (lD d n * (lD d n + 1) * (lD d n + 2)) • πd d eDb v -
        (-((n : ℂ) + 1) * ((n : ℂ) + 1 - pp d) * (lD d n + 2) -
          ((n : ℂ) + 2 - mC d) * (qq d + (n : ℂ) + 2) * lD d n) • πd d eXm v +
        (lD d n / 2) • πd d eXm (πd d eXm (πd d eP v)) ∈ S :=
    S.add_mem (S.sub_mem (S.smul_mem _ (hS.2 _ _ hvS)) (S.smul_mem _ (hS.2 _ _ hvS)))
      (S.smul_mem _ (hS.2 _ _ (hS.2 _ _ (hS.2 _ _ hvS))))
  refine ⟨_, S.smul_mem (((n : ℂ) + 1) * ((n : ℂ) + 1 - mC d) * ((n : ℂ) + 1 - pp d) *
    (lD d n + 2))⁻¹ hu, ?_⟩
  rw [map_smul, ncpL_ladder hv, smul_smul, inv_mul_cancel₀ hc, one_smul]

end ComplexGLTwoNoncompact

end Langlands.Archimedean
