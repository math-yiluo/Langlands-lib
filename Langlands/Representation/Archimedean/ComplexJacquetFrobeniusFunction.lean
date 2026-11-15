import Langlands.Representation.Archimedean.ComplexJacquetChart
import Langlands.Representation.Archimedean.ComplexJacquetBorel
import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Langlands.LinearAlgebra.TriangularUnitary

/-!
# The Frobenius functions of a Jacquet functional

Let `(ρ, π)` be a `(𝔤𝔩_n(ℂ), U(n))`-module on `V` and `ℓ` a linear functional on `V` that
transforms under the diagonal unitary matrices `m` by `m ↦ ∏ⱼ m_jj^{l_j}`
(`IsTorusEigenfunctional`). For exponents `α`, the Frobenius function of `w ∈ V` is
`f_w(g) = χ(β) ℓ(ρ(κ) w)`, where `g = β κ` with `β` upper triangular and `κ` unitary is a chosen
factorization (`iwasawaB`, `iwasawaK`) and `χ = borelChar l α`. This file shows:

* `frobeniusFunction_eq`: the value does not depend on the factorization;
* `frobeniusFunction_translate`: `f_w(b z k) = χ(b) f_{ρ(k) w}(z)` for `b` upper triangular and
  `k` unitary;
* `frobeniusFunction_diagonal_mul`: `f_w(diag(a) u g) = ∏ⱼ borelFactor(l_j, α_j, a_j) f_w(g)`
  for `u` upper unipotent;
* `contMDiff_frobeniusFunction`: for a `(𝔤𝔩_n(ℂ), U(n))`-module, `f_w` is `C^∞`.

The derivatives of `f_w` are computed in `ComplexJacquetFrobeniusProof`.

Smoothness is shown at `1` with the chart `Φ(X) = (1 + P_b X) exp(P_u X)` of
`ComplexJacquetChart`: near `1`, `f_w(Φ(X)) = χ(1 + P_b X) ℓ(ρ(exp P_u X) w)`, and the second
factor is a `C^∞` function of `X` by `IsComplexGKModule.exists_contDiff_coeff`. At
`g₀ = β₀ κ₀` it follows from `f_w(y) = χ(β₀) f_{ρ(κ₀) w}(β₀⁻¹ y κ₀*)`.
-/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.Operator ContDiff Topology Manifold

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

-- As in `GeneralLinear`: the charts on units and the operator norm on matrices need reduction
-- through the normed-ring instances.
set_option backward.isDefEq.respectTransparency false

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.LinearAlgebra.TriangularUnitary

universe uV

/-! ## Iwasawa factors -/

section Iwasawa

variable {n : ℕ}

theorem exists_iwasawa (g : Langlands.GeneralLinear n ℂ) :
    ∃ b u : Matrix (Fin n) (Fin n) ℂ,
      IsTriangularUnitaryFactorization (g : Matrix (Fin n) (Fin n) ℂ) b u :=
  exists_upperTriangular_mul_unitary _ (Units.isUnit g)

/-- A chosen upper triangular factor `β` of `g = β κ`. -/
def iwasawaB (g : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (exists_iwasawa g).choose

/-- The unitary factor `κ` of `g = β κ`. -/
def iwasawaK (g : Langlands.GeneralLinear n ℂ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨(exists_iwasawa g).choose_spec.choose, (exists_iwasawa g).choose_spec.choose_spec.2.2.1⟩

theorem iwasawa_spec (g : Langlands.GeneralLinear n ℂ) :
    (iwasawaB g).IsUpperTriangular ∧ IsUnit (iwasawaB g) ∧
      (g : Matrix (Fin n) (Fin n) ℂ) = iwasawaB g * (iwasawaK g : Matrix (Fin n) (Fin n) ℂ) :=
  let h := (exists_iwasawa g).choose_spec.choose_spec
  ⟨h.1, h.2.1, h.2.2.2⟩

/-- An upper triangular matrix with nonzero diagonal entries is invertible. -/
theorem isUnit_of_upper {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsUpperTriangular)
    (hd : ∀ j, M j j ≠ 0) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular hM, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => hd j

end Iwasawa

/-! ## The Frobenius function -/

section Function

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- `ℓ` transforms under the diagonal unitary matrices `m` by `m ↦ ∏ⱼ m_jj^{l_j}`. -/
def IsTorusEigenfunctional (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (ℓ : V →ₗ[ℂ] ℂ) (l : Fin n → ℤ) : Prop :=
  ∀ m : Matrix.unitaryGroup (Fin n) ℂ,
    (∀ i j, i ≠ j → (m : Matrix (Fin n) (Fin n) ℂ) i j = 0) → ∀ w : V,
      ℓ (ρ m w) = (∏ j, ((m : Matrix (Fin n) (Fin n) ℂ) j j) ^ (l j)) * ℓ w

/-- The Frobenius function `f_w(g) = χ(β) ℓ(ρ(κ) w)` for the chosen factors `g = β κ`, with
`χ = borelChar l α`. -/
def frobeniusFunction (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (ℓ : V →ₗ[ℂ] ℂ) (l : Fin n → ℤ) (α : Fin n → ℂ) (w : V)
    (g : Langlands.GeneralLinear n ℂ) : ℂ :=
  borelChar l α (iwasawaB g) * ℓ (ρ (iwasawaK g) w)

variable {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V} {ℓ : V →ₗ[ℂ] ℂ}
  {l : Fin n → ℤ}

/-- **Independence of the factorization.** If `g = b k` with `b` invertible upper triangular
and `k` unitary, then `f_w(g) = χ(b) ℓ(ρ(k) w)`. The matrix `m = k κ* = b⁻¹ β` is upper
triangular and unitary, hence diagonal with entries of norm one, and its contributions
`χ(m) = ∏ m_jj^{l_j}` and `ℓ ∘ ρ(m*) = ∏ conj(m_jj)^{l_j} ℓ` cancel. -/
theorem frobeniusFunction_eq (hT : IsTorusEigenfunctional ρ ℓ l) (α : Fin n → ℂ) (w : V)
    (g : Langlands.GeneralLinear n ℂ) {b : Matrix (Fin n) (Fin n) ℂ}
    (k : Matrix.unitaryGroup (Fin n) ℂ) (hb : b.IsUpperTriangular) (hbu : IsUnit b)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) = b * (k : Matrix (Fin n) (Fin n) ℂ)) :
    frobeniusFunction ρ ℓ l α w g = borelChar l α b * ℓ (ρ k w) := by
  obtain ⟨hβ, -, hgβ⟩ := iwasawa_spec g
  set β := iwasawaB g with hβdef
  set κ := iwasawaK g with hκdef
  set m : Matrix.unitaryGroup (Fin n) ℂ := k * star κ with hm
  have hκκ : (κ : Matrix (Fin n) (Fin n) ℂ) * star (κ : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.mul_star_self_of_mem κ.2
  have hkk : star (k : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem k.2
  have hmc : (m : Matrix (Fin n) (Fin n) ℂ) =
      (k : Matrix (Fin n) (Fin n) ℂ) * star (κ : Matrix (Fin n) (Fin n) ℂ) := rfl
  have hbm : b * (m : Matrix (Fin n) (Fin n) ℂ) = β := by
    rw [hmc, ← Matrix.mul_assoc, ← hg, hgβ, Matrix.mul_assoc, hκκ, Matrix.mul_one]
  have hbdet : IsUnit b.det := (Matrix.isUnit_iff_isUnit_det b).mp hbu
  let _ : Invertible b := Matrix.invertibleOfIsUnitDet b hbdet
  have hmb : (m : Matrix (Fin n) (Fin n) ℂ) = b⁻¹ * β := by
    rw [← hbm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul b hbdet, Matrix.one_mul]
  have hmu : (m : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular := by
    rw [hmb]
    exact (Matrix.blockTriangular_inv_of_blockTriangular hb).mul hβ
  have hmd := offDiag_eq_zero_of_upper_unitary m.2 hmu
  have hmn := norm_diag_eq_one_of_unitary m.2 hmd
  have hm0 : ∀ j, (m : Matrix (Fin n) (Fin n) ℂ) j j ≠ 0 := fun j => by
    rw [← norm_ne_zero_iff, hmn j]
    exact one_ne_zero
  have hκm : κ = star m * k := by
    apply Subtype.ext
    change (κ : Matrix (Fin n) (Fin n) ℂ) =
      star ((k : Matrix (Fin n) (Fin n) ℂ) * star (κ : Matrix (Fin n) (Fin n) ℂ)) *
        (k : Matrix (Fin n) (Fin n) ℂ)
    rw [star_mul, star_star, Matrix.mul_assoc, hkk, Matrix.mul_one]
  have hsd : ∀ i j, i ≠ j →
      ((star m : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0 := by
    intro i j hij
    change (star (m : Matrix (Fin n) (Fin n) ℂ)) i j = 0
    rw [Matrix.star_apply, hmd j i (Ne.symm hij), star_zero]
  have hprod : (∏ j, ((m : Matrix (Fin n) (Fin n) ℂ) j j) ^ (l j)) *
      ∏ j, (((star m : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) j j) ^ (l j) =
        1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun j _ => ?_
    change ((m : Matrix (Fin n) (Fin n) ℂ) j j) ^ (l j) *
      (star (m : Matrix (Fin n) (Fin n) ℂ)) j j ^ (l j) = 1
    rw [Matrix.star_apply, ← mul_zpow, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hmn j]
    simp
  change borelChar l α β * ℓ (ρ κ w) = _
  rw [← hbm, borelChar_mul l α hb hmu (diag_ne_zero_of_upper hb hbu) hm0, hκm, map_mul,
    Module.End.mul_apply, hT _ hsd, borelChar_of_norm_diag l α hmn]
  rw [mul_assoc, ← mul_assoc (∏ j, ((m : Matrix (Fin n) (Fin n) ℂ) j j) ^ (l j)), hprod,
    one_mul]

/-- **Translation.** If `g = b z k` with `b` invertible upper triangular and `k` unitary, then
`f_w(g) = χ(b) f_{ρ(k) w}(z)`. -/
theorem frobeniusFunction_translate (hT : IsTorusEigenfunctional ρ ℓ l) (α : Fin n → ℂ) (w : V)
    (g z : Langlands.GeneralLinear n ℂ) {b : Matrix (Fin n) (Fin n) ℂ}
    (k : Matrix.unitaryGroup (Fin n) ℂ) (hb : b.IsUpperTriangular) (hbu : IsUnit b)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) =
      b * (z : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ)) :
    frobeniusFunction ρ ℓ l α w g = borelChar l α b * frobeniusFunction ρ ℓ l α (ρ k w) z := by
  obtain ⟨hβ, hβu, hzβ⟩ := iwasawa_spec z
  rw [frobeniusFunction_eq hT α w g (iwasawaK z * k) (hb.mul hβ) (hbu.mul hβu)]
  · unfold frobeniusFunction
    rw [borelChar_mul l α hb hβ (diag_ne_zero_of_upper hb hbu) (diag_ne_zero_of_upper hβ hβu),
      map_mul, Module.End.mul_apply]
    ring
  · rw [hg, hzβ]
    change _ = _ * ((iwasawaK z : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ))
    simp only [Matrix.mul_assoc]

/-- Left multiplication by an upper triangular matrix: `f_w(b g) = χ(b) f_w(g)`. -/
theorem frobeniusFunction_mul_left (hT : IsTorusEigenfunctional ρ ℓ l) (α : Fin n → ℂ) (w : V)
    (b g : Langlands.GeneralLinear n ℂ) (hb : (b : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular) :
    frobeniusFunction ρ ℓ l α w (b * g) =
      borelChar l α (b : Matrix (Fin n) (Fin n) ℂ) * frobeniusFunction ρ ℓ l α w g := by
  have h := frobeniusFunction_translate hT α w (b * g) g 1 hb (Units.isUnit b) (by simp)
  rwa [map_one, Module.End.one_apply] at h

/-- Right multiplication by a unitary matrix: `f_w(g k) = f_{ρ(k) w}(g)`. -/
theorem frobeniusFunction_mul_unitary (hT : IsTorusEigenfunctional ρ ℓ l) (α : Fin n → ℂ)
    (w : V) (g kk : Langlands.GeneralLinear n ℂ) (k : Matrix.unitaryGroup (Fin n) ℂ)
    (hk : (kk : Matrix (Fin n) (Fin n) ℂ) = k) :
    frobeniusFunction ρ ℓ l α w (g * kk) = frobeniusFunction ρ ℓ l α (ρ k w) g := by
  have h := frobeniusFunction_translate hT α w (g * kk) g k Matrix.blockTriangular_one isUnit_one
    (by rw [Units.val_mul, hk, Matrix.one_mul])
  rwa [borelChar_one, one_mul] at h

/-- The principal series transformation law. -/
theorem frobeniusFunction_diagonal_mul (hT : IsTorusEigenfunctional ρ ℓ l) (α : Fin n → ℂ)
    (w : V) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) (g : Langlands.GeneralLinear n ℂ) :
    frobeniusFunction ρ ℓ l α w
        ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
          (u : Langlands.GeneralLinear n ℂ) * g) =
      (∏ j, borelFactor (l j) (α j) (a j)) * frobeniusFunction ρ ℓ l α w g := by
  have hD : (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      (u : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular := by
    rw [Units.val_mul, Iwasawa.diagonalUnits_val]
    exact (Matrix.blockTriangular_diagonal _).mul u.2.1
  rw [frobeniusFunction_mul_left hT α w _ g hD]
  have h := borelChar_diagonalUnits_mul l α a u Matrix.blockTriangular_one
    (fun j => by simp)
  rw [Matrix.mul_one] at h
  rw [Units.val_mul, h, borelChar_one, mul_one]

theorem frobeniusFunction_add (α : Fin n → ℂ) (w w' : V) :
    frobeniusFunction ρ ℓ l α (w + w') =
      frobeniusFunction ρ ℓ l α w + frobeniusFunction ρ ℓ l α w' := by
  funext g
  simp [frobeniusFunction, mul_add]

theorem frobeniusFunction_smul (α : Fin n → ℂ) (c : ℂ) (w : V) :
    frobeniusFunction ρ ℓ l α (c • w) = c • frobeniusFunction ρ ℓ l α w := by
  funext g
  simp only [frobeniusFunction, map_smul, smul_eq_mul, Pi.smul_apply]
  ring

end Function

/-! ## Smoothness -/

section Smooth

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ℓ : V →ₗ[ℂ] ℂ} {l : Fin n → ℤ}

/-- Near `1`, in the chart `Φ`, the Frobenius function is `χ(1 + P_b X) G(P_u X)` with `G` the
`C^∞` extension of `Y ↦ ℓ(ρ(exp Y) w)`. -/
theorem contDiffAt_one_frobeniusFunction (hgk : IsComplexGKModule n ρ π)
    (hT : IsTorusEigenfunctional ρ ℓ l) (α : Fin n → ℂ) (w : V) :
    ContDiffAt ℝ ∞ (unitsExtension (frobeniusFunction ρ ℓ l α w)) 1 := by
  obtain ⟨G, hG, hGe⟩ := hgk.exists_contDiff_coeff w ℓ
  obtain ⟨Ψ, hΨ, hΨ1, hΨt, hΨe⟩ := exists_chartInverse (n := n)
  set F : Matrix (Fin n) (Fin n) ℂ → ℂ :=
    fun X => borelChar l α (1 + upperPart X) * G (skewPart X) with hF
  have hFc : ContDiffAt ℝ ∞ F (Ψ 1) := by
    rw [hΨ1]
    have hb : ContDiffAt ℝ ∞ (borelChar l α) (1 + upperPart (0 : Matrix (Fin n) (Fin n) ℂ)) :=
      contDiffAt_borelChar l α fun j => by simp
    have hf : ContDiffAt ℝ ∞ (fun X : Matrix (Fin n) (Fin n) ℂ => 1 + upperPart X) 0 :=
      (contDiff_const.add (LinearMap.toContinuousLinearMap upperPart).contDiff).contDiffAt
    have h1 : ContDiffAt ℝ ∞
        (fun X : Matrix (Fin n) (Fin n) ℂ => borelChar l α (1 + upperPart X)) 0 :=
      hb.comp (f := fun X : Matrix (Fin n) (Fin n) ℂ => 1 + upperPart X) 0 hf
    have h2 : ContDiffAt ℝ ∞ (fun X : Matrix (Fin n) (Fin n) ℂ => G (skewPart X)) 0 :=
      (hG.comp (LinearMap.toContinuousLinearMap skewPart).contDiff).contDiffAt
    exact h1.mul h2
  have hcomp : ContDiffAt ℝ ∞ (F ∘ Ψ) 1 := hFc.comp 1 hΨ
  refine hcomp.congr_of_eventuallyEq ?_
  have hU : ∀ᶠ y in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), IsUnit y :=
    isOpen_setOf_isUnit_matrix.mem_nhds isUnit_one
  have hD := hΨt.eventually eventually_diag_ne_zero
  filter_upwards [hU, hD, hΨe] with y hy hyd hye
  have hbu : (1 + upperPart (Ψ y)).IsUpperTriangular := one_add_upperPart_isUpperTriangular _
  rw [Function.comp_apply, unitsExtension, dite_eq_left_of_eq_true (eq_true hy),
    frobeniusFunction_eq hT α w hy.unit (skewExp (skewPart (Ψ y)) (star_skewPart (Ψ y))) hbu
      (isUnit_of_upper hbu hyd) (by rw [IsUnit.unit_spec, coe_skewExp]; exact hye.symm)]
  show _ = borelChar l α (1 + upperPart (Ψ y)) * G (skewPart (Ψ y))
  rw [hGe]

/-- **Smoothness at every point.** At `g₀ = β₀ κ₀`,
`f_w(y) = χ(β₀) f_{ρ(κ₀) w}(β₀⁻¹ y κ₀*)` near `g₀`. -/
theorem contDiffAt_frobeniusFunction (hgk : IsComplexGKModule n ρ π)
    (hT : IsTorusEigenfunctional ρ ℓ l) (α : Fin n → ℂ) (w : V)
    (g₀ : Langlands.GeneralLinear n ℂ) :
    ContDiffAt ℝ ∞ (unitsExtension (frobeniusFunction ρ ℓ l α w))
      (g₀ : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨hβ, hβu, hg₀⟩ := iwasawa_spec g₀
  set β := iwasawaB g₀ with hβdef
  set κ := iwasawaK g₀ with hκdef
  have hβdet : IsUnit β.det := (Matrix.isUnit_iff_isUnit_det β).mp hβu
  have hκκ : (κ : Matrix (Fin n) (Fin n) ℂ) * star (κ : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.mul_star_self_of_mem κ.2
  have hκκ' : star (κ : Matrix (Fin n) (Fin n) ℂ) * (κ : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem κ.2
  set L : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun y => β⁻¹ * y * star (κ : Matrix (Fin n) (Fin n) ℂ) with hL
  have hLc : ContDiff ℝ ∞ L := (contDiff_const.mul contDiff_id).mul contDiff_const
  have hL0 : L (g₀ : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    rw [hL]
    dsimp only
    rw [hg₀, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul β hβdet, Matrix.one_mul, hκκ]
  have h1 := contDiffAt_one_frobeniusFunction hgk hT α (ρ κ w)
  rw [← hL0] at h1
  have h2 : ContDiffAt ℝ ∞ (fun y => borelChar l α β *
      unitsExtension (frobeniusFunction ρ ℓ l α (ρ κ w)) (L y)) (g₀ : Matrix (Fin n) (Fin n) ℂ) :=
    contDiffAt_const.mul (h1.comp _ hLc.contDiffAt)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (Units.isUnit g₀)] with y hy
  have hLy : IsUnit (L y) :=
    ((Matrix.isUnit_nonsing_inv_iff.mpr hβu).mul hy).mul
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hκκ))
  rw [unitsExtension, dite_eq_left_of_eq_true (eq_true hy), unitsExtension,
    dite_eq_left_of_eq_true (eq_true hLy)]
  refine frobeniusFunction_translate hT α w hy.unit hLy.unit κ hβ hβu ?_
  rw [IsUnit.unit_spec, IsUnit.unit_spec, hL]
  dsimp only
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv β hβdet, Matrix.one_mul,
    Matrix.mul_assoc, hκκ', Matrix.mul_one]

/-- **The Frobenius function is smooth.** -/
theorem contMDiff_frobeniusFunction (hgk : IsComplexGKModule n ρ π)
    (hT : IsTorusEigenfunctional ρ ℓ l) (α : Fin n → ℂ) (w : V) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (frobeniusFunction ρ ℓ l α w) := by
  refine contMDiff_of_contDiffOn (ψ := unitsExtension (frobeniusFunction ρ ℓ l α w)) ?_
    fun g => (unitsExtension_val _ g).symm
  intro y hy
  obtain ⟨g, rfl⟩ := hy
  exact (contDiffAt_frobeniusFunction hgk hT α w g).contDiffWithinAt

end Smooth

end Langlands.Archimedean
