import Langlands.Representation.Archimedean.RealTemperedCommutantReduction
import Langlands.Representation.Archimedean.RealBlockRotation
import Langlands.Representation.Archimedean.RealBlockJacquetFunctional
import Langlands.Representation.Archimedean.RealKTypeTransport
import Langlands.Representation.Archimedean.RealInductionStagesFourier

/-!
# Evaluation functionals of `O(n)`-equivariant maps into real standard modules

For an `O(n)`-equivariant linear map `L` from the `O(n)`-finite functions of one real standard
module into those of another, the value `(L u)(1)` controls `L u` on `O(n)`. This module proves
three facts about these values, and an abstract scalar step built on them.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealDiscreteScalar

open RealTemperedCommutantReduction

variable {n : ℕ}

/-- A linear map between the `O(n)`-finite functions of two real standard modules commutes with
right translation by `O(n)`. -/
def IsKEquivariant {es ds : List RealBlock} (L : KF n es →ₗ[ℂ] KF n ds) : Prop :=
  ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (u : KF n es),
    L (realStandardRep n es k u) = realStandardRep n ds k (L u)

/-- The value at `1` of a vector of `KF n ds`. -/
def ev {ds : List RealBlock} (f : KF n ds) : ℂ :=
  (f : Langlands.GeneralLinear n ℝ → ℂ) 1

theorem ev_rep {ds : List RealBlock} (k : Matrix.unitaryGroup (Fin n) ℝ) (f : KF n ds) :
    ev (realStandardRep n ds k f) = (f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits k) := by
  unfold ev
  rw [realStandardRep_apply_coe]
  change (f : Langlands.GeneralLinear n ℝ → ℂ) (1 * Unitary.toUnits k) = _
  rw [one_mul]

/-- The value of `L u` at `k ∈ O(n)` is the value at `1` of `L` applied to the translate. -/
theorem apply_toUnits {es ds : List RealBlock} {L : KF n es →ₗ[ℂ] KF n ds}
    (hL : IsKEquivariant L) (u : KF n es) (k : Matrix.unitaryGroup (Fin n) ℝ) :
    ((L u : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits k) =
      ev (L (realStandardRep n es k u)) := by
  rw [hL, ev_rep]

/-- A vector that vanishes on `O(n)` is zero. -/
theorem eq_zero_of_toUnits {ds : List RealBlock} (f : KF n ds)
    (hf : ∀ k : Matrix.unitaryGroup (Fin n) ℝ,
      (f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits k) = 0) : f = 0 := by
  apply eq_zero_of_compact_eval
  intro k
  rw [kFiniteEval_apply]
  exact (ev_rep k f).trans (hf k)

/-! ## The abstract scalar step -/

/-- **Scalar step.** Let `Φ` be `O(n)`-equivariant, and let `u_i` be vectors such that for every
`O(n)`-equivariant `L` the values `(L u_i)(1)` are `ε_i (L u_{i₀})(1)`. Then every endomorphism
`E` of `KF n ds` commuting with `O(n)` has a scalar `a` with `E (Φ w) = a Φ w` for every `w` whose
`O(n)`-translates are combinations `R(k) w = Σ_i c(k, i) u_i`. -/
theorem exists_smul_family {es ds : List RealBlock} {ι : Type*} [Fintype ι]
    (Φ : KF n es →ₗ[ℂ] KF n ds) (hΦ : IsKEquivariant Φ) (u : ι → KF n es) (ε : ι → ℂ) (i₀ : ι)
    (hrel : ∀ L : KF n es →ₗ[ℂ] KF n ds, IsKEquivariant L → ∀ i, ev (L (u i)) = ε i * ev (L (u i₀)))
    (E : Module.End ℂ (KF n ds))
    (hE : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (v : KF n ds),
      E (realStandardRep n ds k v) = realStandardRep n ds k (E v)) :
    ∃ a : ℂ, ∀ (w : KF n es) (c : Matrix.unitaryGroup (Fin n) ℝ → ι → ℂ),
      (∀ k, realStandardRep n es k w = ∑ i, c k i • u i) → E (Φ w) = a • Φ w := by
  have hEΦ : IsKEquivariant (E ∘ₗ Φ) := by
    intro k v
    simp only [LinearMap.comp_apply]
    rw [hΦ, hE]
  -- the values on `O(n)` of `L w`
  have hval : ∀ (w : KF n es) (c : Matrix.unitaryGroup (Fin n) ℝ → ι → ℂ),
      (∀ k, realStandardRep n es k w = ∑ i, c k i • u i) →
      ∀ L : KF n es →ₗ[ℂ] KF n ds, IsKEquivariant L →
      ∀ k : Matrix.unitaryGroup (Fin n) ℝ,
        ((L w : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits k) =
          (∑ i, c k i * ε i) * ev (L (u i₀)) := by
    intro w c hexp L hL k
    rw [apply_toUnits hL, hexp, map_sum]
    unfold ev
    rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    have := hrel L hL i
    unfold ev at this
    rw [this]
    ring
  by_cases h1 : ev (Φ (u i₀)) = 0
  · refine ⟨0, fun w c hexp => ?_⟩
    have hw0 : Φ w = 0 := eq_zero_of_toUnits _ fun k => by rw [hval w c hexp Φ hΦ k, h1, mul_zero]
    rw [hw0, map_zero, smul_zero]
  · refine ⟨ev (E (Φ (u i₀))) / ev (Φ (u i₀)), fun w c hexp => ?_⟩
    rw [← sub_eq_zero]
    apply eq_zero_of_toUnits
    intro k
    rw [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    have hE' := hval w c hexp (E ∘ₗ Φ) hEΦ k
    simp only [LinearMap.comp_apply] at hE'
    rw [hE', hval w c hexp Φ hΦ k]
    field_simp
    ring

/-! ## Vanishing along a discrete-series block -/

/-- The block rotation as an element of `O(n)`. -/
def rot (n p : ℕ) (θ : ℝ) : Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨(blockRotation n p θ : Matrix (Fin n) (Fin n) ℝ), blockRotation_mem_unitaryCompact n p θ⟩

theorem toUnits_rot (n p : ℕ) (θ : ℝ) : Unitary.toUnits (rot n p θ) = blockRotation n p θ :=
  Units.ext rfl

/-- **Fourier vanishing.** Let `ds` have an induction block `d` at position `p`, and let `u`
transform under the rotations `r_p(θ)` by `e^{i w θ}` with `|w| ≤ |m|`, `m = d.weight`. Then
`(L u)(1) = 0` for every `O(n)`-equivariant `L` into `KF n ds`. For `|w| < |m|` this is the
block Fourier condition at `1`; for `|w| = |m|` it is the parity of the block modes. -/
theorem ev_eq_zero_of_rotation {es ds : List RealBlock} (hn : realRank ds = n)
    {L : KF n es →ₗ[ℂ] KF n ds} (hL : IsKEquivariant L) {p : ℕ} {d : ComplexCharacterData}
    (hd : realInducedBlockAt ds p = some d) (u : KF n es) (w : ℤ)
    (hw : ∀ θ : ℝ, realStandardRep n es (rot n p θ) u =
      Complex.exp ((w : ℂ) * (θ : ℂ) * Complex.I) • u)
    (hle : |w| ≤ |d.weight|) : ev (L u) = 0 := by
  set f : KF n ds := L u with hf
  have hp : p + 1 < n := hn ▸ realInducedBlockAt_lt hd
  -- values along the rotations
  have hrotval : ∀ θ : ℝ, (f : Langlands.GeneralLinear n ℝ → ℂ) (blockRotation n p θ * 1) =
      Complex.exp ((w : ℂ) * (θ : ℂ) * Complex.I) * ev f := by
    intro θ
    rw [mul_one, ← toUnits_rot, hf, apply_toUnits hL, hw, map_smul]
    unfold ev
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  -- the Fourier coefficient at `1` is `2π (L u)(1)`
  have hcoef : blockFourierCoefficient n p w (f : Langlands.GeneralLinear n ℝ → ℂ) 1 =
      (2 * Real.pi : ℂ) * ev f := by
    unfold blockFourierCoefficient
    have : ∀ θ : ℝ, (f : Langlands.GeneralLinear n ℝ → ℂ) (blockRotation n p θ * 1) *
        Complex.exp (-((w : ℂ) * (θ : ℂ) * Complex.I)) = ev f := by
      intro θ
      rw [hrotval, mul_comm (Complex.exp _) (ev f), mul_assoc, ← Complex.exp_add, add_neg_cancel,
        Complex.exp_zero, mul_one]
    simp_rw [this]
    rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
    push_cast
    ring
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_pos
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  rcases lt_or_eq_of_le hle with hlt | heq
  · have h0 := f.2.1.2 p d hd w hlt 1
    rw [hcoef] at h0
    exact (mul_eq_zero.mp h0).resolve_left h2pi
  · -- parity: the modes of the block have the parity of `|m| + 1`
    obtain ⟨h1, h2, -, -⟩ := RealKTypeTransport.realInducedBlockAt_eq_some hd
    have hpar : (-1 : ℂ) ^ ((d.weight.natAbs : ℤ) + 1) =
        realPositionCharacter ds p (-1) * realPositionCharacter ds (p + 1) (-1) := by
      rw [h1, h2, InductionStages.realInducedFirstCharacter_neg_one,
        InductionStages.realInducedSecondCharacter_neg_one, mul_one]
      norm_cast
    have hodd : ¬ Even (w - ((d.weight.natAbs : ℤ) + 1)) := by
      have hw' : |w| = (d.weight.natAbs : ℤ) := by rw [heq, Int.natCast_natAbs]
      rcases abs_choice w with h | h <;> rw [h] at hw' <;>
        · intro hev
          obtain ⟨r, hr⟩ := hev
          omega
    have h0 := RealBlockJacquet.blockFourierCoefficient_eq_zero_of_not_even hp hpar f hodd 1
    rw [hcoef] at h0
    exact (mul_eq_zero.mp h0).resolve_left h2pi

/-! ## Sign matrices -/

/-- **Sign law.** For a diagonal sign matrix `s ∈ O(n)` with signs `a`, `(L (R(s) u))(1)` is the
principal-series character of `ds` at `a` times `(L u)(1)`. -/
theorem ev_rep_sign {es ds : List RealBlock} {L : KF n es →ₗ[ℂ] KF n ds}
    (hL : IsKEquivariant L) (a : Fin n → ℝˣ) (s : Matrix.unitaryGroup (Fin n) ℝ)
    (hs : Unitary.toUnits s = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ))
    (u : KF n es) :
    ev (L (realStandardRep n es s u)) =
      principalSeriesCharacter ℝ n (realPositionCharacter ds) a * ev (L u) := by
  rw [← apply_toUnits hL, hs]
  have h := (L u).2.1.1.2 a 1 1
  unfold ev
  simpa using h

end RealDiscreteScalar

end Langlands.Archimedean
