import Langlands.Representation.Shahidi.OpenCellShintani
import Langlands.Representation.Conductor.SphericalHomogeneity

/-! # Convergence of the Jacquet integrals at the torus points

For `ψ` of conductor `𝒪` and parameters `(X a, c)` with `|X|` small, the Jacquet integrand of the two-block section is
integrable at every torus point `ϖ^μ`. The proof translates `ϖ^μ` through the open cell
(`w u'(Y) ϖ^μ = diag(h₁, h₂) w u'(h₂⁻¹ Y h₁)`), bounds the spherical Whittaker functions at
`u ϖ^ρ` by `C R^(∑ |ρ_i|)`, uses the homogeneity `W°(u ϖ^ρ; X a) = X^(∑ ρ) W°(u ϖ^ρ; a)` and
counts the classes of depth `D` (at most `q^((r+1)(t+1)D)`). -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa MeasureTheory
open scoped ENNReal NNReal

section Bounds

/-- `‖y ^ e‖ ≤ max(‖y‖, ‖y‖⁻¹) ^ |e|`. -/
theorem norm_zpow_le_max {y : ℂ} (hy : y ≠ 0) (e : ℤ) :
    ‖y ^ e‖ ≤ max ‖y‖ ‖y‖⁻¹ ^ e.natAbs := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  rw [norm_zpow]
  rcases le_or_gt 0 e with he | he
  · have : e = (e.natAbs : ℤ) := (Int.natAbs_of_nonneg he).symm
    rw [this, zpow_natCast, Int.natAbs_natCast]
    exact pow_le_pow_left₀ hy0.le (le_max_left _ _) _
  · have : e = -(e.natAbs : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hy0.le) (le_max_right _ _) _

theorem one_le_max_norm_inv {y : ℂ} (hy : y ≠ 0) : 1 ≤ max ‖y‖ ‖y‖⁻¹ := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  rcases le_or_gt 1 ‖y‖ with h | h
  · exact h.trans (le_max_left _ _)
  · exact (one_le_inv₀ hy0).2 h.le |>.trans (le_max_right _ _)

/-- A bound `‖s_ρ(x)‖ ≤ C R^(∑ |ρ_i|)` for every antitone `ρ`. -/
theorem exists_norm_satakeSchur_le {n : ℕ} (x : Fin (n + 1) → ℂˣ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ ρ : Fin (n + 1) → ℤ, Antitone ρ →
      ‖satakeSchur x ρ‖ ≤ C * R ^ (∑ i, (ρ i).natAbs) := by
  set M : ℝ := 1 + ∑ i, ‖(x i : ℂ)‖ with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ∑ i, ‖(x i : ℂ)‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  have hxM : ∀ i, ‖(x i : ℂ)‖ ≤ M := by
    intro i
    have := Finset.single_le_sum (f := fun i => ‖(x i : ℂ)‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  set y : ℂ := ∏ i, (x i : ℂ) with hy
  have hy0 : y ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (x i).ne_zero
  set P := max ‖y‖ ‖y‖⁻¹ with hP
  have hP1 : 1 ≤ P := one_le_max_norm_inv hy0
  set C0 : ℝ := ((n + 1).factorial : ℝ) * (2 ^ (2 * (n + 1)) * M ^ (n + 1)) ^ (n + 1) with hC0
  set R0 : ℝ := 2 ^ (n + 1) * M ^ (2 * (n + 1)) with hR0
  have hR01 : 1 ≤ R0 := by
    have h1 : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ M ^ (2 * (n + 1)) := one_le_pow₀ hM1
    nlinarith
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨C0, P * R0 ^ (n + 2), hC00, one_le_mul_of_one_le_of_one_le hP1 (one_le_pow₀ hR01), ?_⟩
  intro ρ hρ
  set e := ρ (Fin.last n) with he
  set ρ' : Fin (n + 1) → ℤ := fun i => ρ i - e with hρ'
  have hρ'a : Antitone ρ' := fun i j hij => by simp only [hρ']; linarith [hρ hij]
  have hρ'l : ρ' (Fin.last n) = 0 := by simp [hρ', he]
  have hρ'n : ∀ i, 0 ≤ ρ' i := fun i => by
    have := hρ (Fin.le_last i)
    simp only [hρ']
    linarith
  set D := (∑ i, ρ' i).toNat with hD
  have hDz : ∑ i, ρ' i = (D : ℤ) :=
    (Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hρ'n i)).symm
  have hb := norm_satakeSchur_le x hM1 hxM hρ'a (by rw [hρ'l]) hDz
  have hs : satakeSchur x ρ = y ^ e * satakeSchur x ρ' := by
    have hfun : (fun i => ρ' i - 0) = fun i => ρ i - ρ (Fin.last n) := by
      funext i
      rw [sub_zero]
    unfold satakeSchur
    rw [hρ'l, zpow_zero, one_mul, hfun]
  -- the exponents
  set A := ∑ i, (ρ i).natAbs with hA
  have heA : e.natAbs ≤ A := by
    rw [hA]
    exact Finset.single_le_sum (f := fun i => (ρ i).natAbs) (fun i _ => Nat.zero_le _)
      (Finset.mem_univ (Fin.last n))
  have hDA : D ≤ (n + 2) * A := by
    have h1 : (D : ℤ) ≤ ∑ i, |ρ i| + (n + 1) * |e| := by
      rw [← hDz]
      simp only [hρ', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have h2 : ∑ i, ρ i ≤ ∑ i, |ρ i| := Finset.sum_le_sum fun i _ => le_abs_self _
      have h3 : -((n + 1 : ℕ) : ℤ) * e ≤ (n + 1) * |e| := by
        have := neg_abs_le e
        push_cast
        nlinarith
      push_cast at h3 ⊢
      linarith
    have h4 : (∑ i, |ρ i|) = (A : ℤ) := by
      rw [hA]
      push_cast
      rfl
    have h5 : |e| = (e.natAbs : ℤ) := Int.abs_eq_natAbs e
    rw [h4, h5] at h1
    have h6 : (e.natAbs : ℤ) ≤ A := by exact_mod_cast heA
    have : (D : ℤ) ≤ ((n + 2) * A : ℕ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  rw [hs, norm_mul]
  calc ‖y ^ e‖ * ‖satakeSchur x ρ'‖ ≤ P ^ e.natAbs * (C0 * R0 ^ D) :=
        mul_le_mul (norm_zpow_le_max hy0 e) hb (norm_nonneg _) (by positivity)
    _ ≤ P ^ A * (C0 * (R0 ^ (n + 2)) ^ A) := by
        apply mul_le_mul (pow_le_pow_right₀ hP1 heA)
          (mul_le_mul_of_nonneg_left (by
            rw [← pow_mul]
            exact pow_le_pow_right₀ hR01 hDA) hC00) (by positivity) (by positivity)
    _ = C0 * (P * R0 ^ (n + 2)) ^ A := by rw [mul_left_comm, ← mul_pow]

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation F Γ₀} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ) {n : ℕ}
  {θ : upperUnipotent (n + 1) F →* ℂˣ}

/-- For an integrally trivial unitary `θ` and `q ≥ 1`, a bound `‖W°(u ϖ^ρ; x)‖ ≤ C R^(∑ |ρ_i|)`
for every upper unipotent `u` and every exponent `ρ`. -/
theorem exists_norm_sphericalWhittaker_le (hθ : IsIntegrallyTrivial v θ)
    (hθ1 : ∀ w, ‖(θ w : ℂ)‖ = 1) {q : ℕ} (hq : 1 ≤ q) (x : Fin (n + 1) → ℂˣ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ (u : Langlands.GeneralLinear (n + 1) F),
      u ∈ upperUnipotent (n + 1) F → ∀ (ρ : Fin (n + 1) → ℤ),
      ‖sphericalWhittaker hϖ θ q x (u * torus ϖ ρ)‖ ≤ C * R ^ (∑ i, (ρ i).natAbs) := by
  obtain ⟨C, R, hC, hR, h⟩ := exists_norm_satakeSchur_le x
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨C, (q : ℝ) ^ n * R, hC, one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq1) hR, ?_⟩
  intro u hu ρ
  by_cases hρ : Antitone ρ
  · rw [sphericalWhittaker_unipotent_mul_torus hϖ hθ q x hu hρ, norm_mul, hθ1, one_mul,
      norm_mul]
    have hh := norm_halfModulus_le hq ρ (D := ∑ i, (ρ i).natAbs) (by
      push_cast
      exact le_refl _)
    calc ‖halfModulus q ρ‖ * ‖satakeSchur x ρ‖ ≤
          (q : ℝ) ^ (n * ∑ i, (ρ i).natAbs) * (C * R ^ (∑ i, (ρ i).natAbs)) :=
          mul_le_mul hh (h ρ hρ) (norm_nonneg _) (by positivity)
      _ = C * ((q : ℝ) ^ n * R) ^ (∑ i, (ρ i).natAbs) := by
          rw [mul_pow, pow_mul]
          ring
  · rw [sphericalWhittaker_unipotent_mul_torus_of_not_antitone hϖ q x hu hρ, norm_zero]
    positivity

/-- **Homogeneity of the spherical Whittaker function in its parameter**, for an integrally
trivial `θ`. -/
theorem sphericalWhittaker_smul_unipotent_mul_torus (hθ : IsIntegrallyTrivial v θ) (q : ℕ)
    (z : ℂˣ) (x : Fin (n + 1) → ℂˣ) {u : Langlands.GeneralLinear (n + 1) F}
    (hu : u ∈ upperUnipotent (n + 1) F) (ρ : Fin (n + 1) → ℤ) :
    sphericalWhittaker hϖ θ q (fun i => z * x i) (u * torus ϖ ρ) =
      (z : ℂ) ^ (∑ i, ρ i) * sphericalWhittaker hϖ θ q x (u * torus ϖ ρ) := by
  by_cases hρ : Antitone ρ
  · rw [sphericalWhittaker_unipotent_mul_torus hϖ hθ q _ hu hρ,
      sphericalWhittaker_unipotent_mul_torus hϖ hθ q _ hu hρ, satakeSchur_scale]
    ring
  · rw [sphericalWhittaker_unipotent_mul_torus_of_not_antitone hϖ q _ hu hρ,
      sphericalWhittaker_unipotent_mul_torus_of_not_antitone hϖ q _ hu hρ, mul_zero]

end Bounds

section Translation

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocConvTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocConvValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocConvLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocConvT2Space : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocConvSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocConvMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocConvBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
variable {r t : ℕ}
variable {Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
    Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}

/-- `w u'(Y) diag'(h₂, h₁) = diag(h₁, h₂) w u'(h₂⁻¹ Y h₁)`. -/
theorem blockWeyl_mul_intertwiningUnipotent_mul_swap (h₂ : Langlands.GeneralLinear (t + 1) K.Carrier)
    (h₁ : Langlands.GeneralLinear (r + 1) K.Carrier) (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    blockWeyl (r + 1) (t + 1) K.Carrier * intertwiningUnipotent (r + 1) (t + 1) K.Carrier Y *
        swapRank (r + 1) (t + 1) K.Carrier (blockSum (h₂, h₁)) =
      blockSum (h₁, h₂) * (blockWeyl (r + 1) (t + 1) K.Carrier *
        intertwiningUnipotent (r + 1) (t + 1) K.Carrier (rectangularConj h₂ h₁ Y)) := by
  rw [rectangularConj_apply, intertwiningUnipotent, intertwiningUnipotent, mul_assoc, ← map_mul,
    upper_mul_blockSum, map_mul, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← blockWeyl_conjugate_blockSum (r + 1) (t + 1) K.Carrier h₂ h₁, inv_mul_cancel_right]

/-- `diag(h₁, h₂) u(X) = u(h₁ X h₂⁻¹) diag(h₁, h₂)`. -/
theorem blockSum_mul_upper (h₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (h₂ : Langlands.GeneralLinear (t + 1) K.Carrier) (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier) :
    blockSum (h₁, h₂) * upper (r + 1) (t + 1) K.Carrier X =
      upper (r + 1) (t + 1) K.Carrier ((h₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) K.Carrier) * X *
        ((h₂⁻¹ : Langlands.GeneralLinear (t + 1) K.Carrier) : Matrix (Fin (t + 1)) (Fin (t + 1)) K.Carrier)) *
        blockSum (h₁, h₂) := by
  rw [upper_mul_blockSum]
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
    Units.inv_mul, Matrix.mul_one]

/-- The lift translated by `diag(h₁, h₂)` on the open cell. -/
def translatedLower (Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
      Langlands.GeneralLinear (t + 1) K.Carrier → ℂ)
    (h₁ : Langlands.GeneralLinear (r + 1) K.Carrier) (h₂ : Langlands.GeneralLinear (t + 1) K.Carrier)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) : ℂ :=
  liftFunction hϖ Φ (blockSum (h₁, h₂) * lower (r + 1) (t + 1) K.Carrier Y)

/-- For a Levi-invariant `Φ`, the Jacquet integrand at `diag'(h₂, h₁)` through the change of
variables `Y ↦ h₂⁻¹ Y h₁`. -/
theorem jacquetIntegrandAt_swap (hΦ : IsLeviInvariant Φ)
    (h₂ : Langlands.GeneralLinear (t + 1) K.Carrier) (h₁ : Langlands.GeneralLinear (r + 1) K.Carrier) :
    jacquetIntegrandAt ψ hϖ Φ (swapRank (r + 1) (t + 1) K.Carrier (blockSum (h₂, h₁))) =
      fun Y => intertwiningJacquetKernel r t ψ Y *
        translatedLower hϖ Φ h₁ h₂ (rectangularConj h₂ h₁ Y) := by
  funext Y
  rw [jacquetIntegrandAt_apply, blockWeyl_mul_intertwiningUnipotent_mul_swap,
    blockWeyl_mul_intertwiningUnipotent, ← mul_assoc,
    liftFunction_mul_integral hϖ hΦ _ _ (blockWeyl_mem_integralSubgroup K r t)]
  rfl

theorem isLatticePeriodic_translatedLower (hΦ : IsLeviInvariant Φ)
    (h₁ : Langlands.GeneralLinear (r + 1) K.Carrier) (h₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    IsLatticePeriodic K (translatedLower hϖ Φ h₁ h₂) := by
  intro Y Z hZ
  unfold translatedLower
  rw [lower_add, ← mul_assoc, liftFunction_mul_integral hϖ hΦ _ _ (lower_mem_integralSubgroup Z hZ)]

/-- For a Levi-invariant `Φ`, the translated lift is `Φ` at the translated open-cell Levi
components. -/
theorem translatedLower_eq (hΦ : IsLeviInvariant Φ)
    (h₁ : Langlands.GeneralLinear (r + 1) K.Carrier) (h₂ : Langlands.GeneralLinear (t + 1) K.Carrier)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    ∃ u₁ ∈ upperUnipotent (r + 1) K.Carrier, ∃ u₂ ∈ upperUnipotent (t + 1) K.Carrier,
      translatedLower hϖ Φ h₁ h₂ Y =
        Φ (h₁ * (u₁ * Iwasawa.torus ϖ fun i => openCellExponent hϖ Y (i.castAdd (t + 1))))
          (h₂ * (u₂ * Iwasawa.torus ϖ fun j => openCellExponent hϖ Y (j.natAdd (r + 1)))) := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_openCellExponent hϖ Y
  have hb := isUpperTriangular_mul_torus hu ϖ (openCellExponent hϖ Y)
  have hb' := eq_upper_mul_blockSum (u * Iwasawa.torus ϖ (openCellExponent hϖ Y)) hb
  rw [topLeft_mul_torus hu, botRight_mul_torus hu] at hb'
  refine ⟨topLeft u hu.1, topLeft_mem_upperUnipotent hu, botRight u hu.1,
    botRight_mem_upperUnipotent hu, ?_⟩
  unfold translatedLower
  rw [h, hb', ← mul_assoc, ← mul_assoc, blockSum_mul_upper, mul_assoc (upper _ _ _ _), ← map_mul,
    Prod.mk_mul_mk, liftFunction_law hϖ hΦ _ _ _ k hk]

include hϖ in
/-- The modulus of the section at `(u₁ ϖ^(ρ₁), u₂ ϖ^(ρ₂))`. -/
theorem twoBlockModulus_unipotent_mul_torus {u₁ : Langlands.GeneralLinear (r + 1) K.Carrier}
    (hu₁ : u₁ ∈ upperUnipotent (r + 1) K.Carrier) {u₂ : Langlands.GeneralLinear (t + 1) K.Carrier}
    (hu₂ : u₂ ∈ upperUnipotent (t + 1) K.Carrier) (ρ₁ : Fin (r + 1) → ℤ) (ρ₂ : Fin (t + 1) → ℤ) :
    twoBlockModulus K (u₁ * Iwasawa.torus ϖ ρ₁) (u₂ * Iwasawa.torus ϖ ρ₂) =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^
        (((r + 1 : ℕ) : ℤ) * ∑ j, ρ₂ j - ((t + 1 : ℕ) : ℤ) * ∑ i, ρ₁ i) := by
  have hq : (K.canonicalTopologicalData.residueCardinality : ℝ) ≠ 0 := by
    have := residueCardinality_pos K
    positivity
  rw [twoBlockModulus, determinantNorm_unipotent_mul_torus K hϖ hu₁,
    determinantNorm_unipotent_mul_torus K hϖ hu₂, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
    ← zpow_mul, ← zpow_sub₀ hq]
  congr 1
  push_cast
  ring

/-- The norm of the section at `(u₁ ϖ^(ρ₁), u₂ ϖ^(ρ₂))`. -/
theorem norm_fullΦ_unipotent_mul_torus (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    {u₁ : Langlands.GeneralLinear (r + 1) K.Carrier} (hu₁ : u₁ ∈ upperUnipotent (r + 1) K.Carrier)
    {u₂ : Langlands.GeneralLinear (t + 1) K.Carrier} (hu₂ : u₂ ∈ upperUnipotent (t + 1) K.Carrier)
    (ρ₁ : Fin (r + 1) → ℤ) (ρ₂ : Fin (t + 1) → ℤ) :
    ‖Base.fullΦ ψ hϖ a c s (u₁ * Iwasawa.torus ϖ ρ₁) (u₂ * Iwasawa.torus ϖ ρ₂)‖ =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^
          (((((r + 1 : ℕ) : ℤ) * ∑ j, ρ₂ j - ((t + 1 : ℕ) : ℤ) * ∑ i, ρ₁ i : ℤ) : ℝ) *
            (1 / 2 + s.re / ((r + t + 2 : ℕ) : ℝ))) *
        ‖GeneralLinear.Spherical.sphericalWhittaker (n := r) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
          K.canonicalTopologicalData.residueCardinality a (u₁ * Iwasawa.torus ϖ ρ₁)‖ *
        ‖GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
          K.canonicalTopologicalData.residueCardinality c (u₂ * Iwasawa.torus ϖ ρ₂)‖ := by
  have hq : (0 : ℝ) < K.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast residueCardinality_pos K
  unfold Base.fullΦ
  rw [norm_mul, norm_mul, twoBlockModulus_unipotent_mul_torus hϖ hu₁ hu₂,
    Complex.norm_cpow_eq_rpow_re_of_pos (zpow_pos hq _), ← Real.rpow_intCast,
    ← Real.rpow_mul hq.le]
  have hre : ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ)).re =
      1 / 2 + s.re / ((r + t + 2 : ℕ) : ℝ) := by
    rw [Complex.add_re, Complex.div_natCast_re]
    norm_num
  rw [hre]

/-- `ϖ^μ (u ϖ^ρ) = (ϖ^μ u ϖ^(-μ)) ϖ^(μ + ρ)`. -/
theorem torus_mul_unipotent_mul_torus {n : ℕ} (μ ρ : Fin n → ℤ) (u : Langlands.GeneralLinear n K.Carrier) :
    Iwasawa.torus ϖ μ * (u * Iwasawa.torus ϖ ρ) =
      (Iwasawa.torus ϖ μ * u * (Iwasawa.torus ϖ μ)⁻¹) * Iwasawa.torus ϖ (μ + ρ) := by
  rw [← RankinSelberg.UnramifiedWhittaker.torus_mul_torus]
  group

theorem natAbs_sum_add_le {n : ℕ} (μ ρ : Fin n → ℤ) :
    ∑ i, (μ i + ρ i).natAbs ≤ ∑ i, (μ i).natAbs + ∑ i, (ρ i).natAbs := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem sum_natAbs_of_nonneg {n : ℕ} {ρ : Fin n → ℤ} (h : ∀ i, 0 ≤ ρ i) :
    ((∑ i, (ρ i).natAbs : ℕ) : ℤ) = ∑ i, ρ i := by
  push_cast
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (h i)

theorem sum_natAbs_of_nonpos {n : ℕ} {ρ : Fin n → ℤ} (h : ∀ i, ρ i ≤ 0) :
    ((∑ i, (ρ i).natAbs : ℕ) : ℤ) = -∑ i, ρ i := by
  push_cast
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => abs_of_nonpos (h i)

include hϖ in
/-- **The bound for the translated lift with scaled first parameter**, for `ψ` of conductor `𝒪`
and the given bounds for `W°(·; a)` and `W°(·; c)`. -/
theorem norm_translatedLower_fullΦ_le (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ) {Ca Ra Cc Rc : ℝ}
    (hCa : 0 ≤ Ca) (hRa : 1 ≤ Ra) (hCc : 0 ≤ Cc) (hRc : 1 ≤ Rc)
    (hWa : ∀ u : Langlands.GeneralLinear (r + 1) K.Carrier, u ∈ upperUnipotent (r + 1) K.Carrier →
      ∀ ρ : Fin (r + 1) → ℤ,
      ‖GeneralLinear.Spherical.sphericalWhittaker (n := r) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
          K.canonicalTopologicalData.residueCardinality a (u * Iwasawa.torus ϖ ρ)‖ ≤
        Ca * Ra ^ (∑ i, (ρ i).natAbs))
    (hWc : ∀ u : Langlands.GeneralLinear (t + 1) K.Carrier, u ∈ upperUnipotent (t + 1) K.Carrier →
      ∀ ρ : Fin (t + 1) → ℤ,
      ‖GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
          K.canonicalTopologicalData.residueCardinality c (u * Iwasawa.torus ϖ ρ)‖ ≤
        Cc * Rc ^ (∑ j, (ρ j).natAbs))
    (X : ℂˣ) (μ₁ : Fin (r + 1) → ℤ) (μ₂ : Fin (t + 1) → ℤ)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    ‖translatedLower hϖ (Base.fullΦ ψ hϖ (fun i => X * a i) c s) (Iwasawa.torus ϖ μ₁)
        (Iwasawa.torus ϖ μ₂) Y‖ ≤
      ((K.canonicalTopologicalData.residueCardinality : ℝ) ^
          (((((r + 1 : ℕ) : ℤ) * ∑ j, μ₂ j - ((t + 1 : ℕ) : ℤ) * ∑ i, μ₁ i : ℤ) : ℝ) *
            (1 / 2 + s.re / ((r + t + 2 : ℕ) : ℝ))) *
          ‖(X : ℂ)‖ ^ (∑ i, μ₁ i) * (Ca * Ra ^ (∑ i, (μ₁ i).natAbs)) *
          (Cc * Rc ^ (∑ j, (μ₂ j).natAbs))) *
        ((K.canonicalTopologicalData.residueCardinality : ℝ) ^
            (-((r + t + 2 : ℕ) : ℝ) * (1 / 2 + s.re / ((r + t + 2 : ℕ) : ℝ))) *
          ‖(X : ℂ)‖ * Ra * Rc) ^ (openCellDepth hϖ Y).toNat := by
  have hq : (0 : ℝ) < K.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast residueCardinality_pos K
  have hX0 : ‖(X : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 X.ne_zero
  have hΦX := Base.isLeviInvariant_fullΦ hϖ hψ (fun i => X * a i) c s
  have hθa := isIntegrallyTrivial_of_additiveConductor K hψ r
  obtain ⟨u₁, hu₁, u₂, hu₂, heq⟩ := translatedLower_eq hϖ hΦX (Iwasawa.torus ϖ μ₁)
    (Iwasawa.torus ϖ μ₂) Y
  set lam : Fin (r + 1) → ℤ := fun i => openCellExponent hϖ Y (i.castAdd (t + 1)) with hlam
  set nu : Fin (t + 1) → ℤ := fun j => openCellExponent hϖ Y (j.natAdd (r + 1)) with hnu
  have hv₁ := RankinSelberg.UnramifiedWhittaker.torus_conj_mem_upperUnipotent ϖ μ₁ hu₁
  have hv₂ := RankinSelberg.UnramifiedWhittaker.torus_conj_mem_upperUnipotent ϖ μ₂ hu₂
  rw [heq, torus_mul_unipotent_mul_torus, torus_mul_unipotent_mul_torus,
    norm_fullΦ_unipotent_mul_torus ψ hϖ _ c s hv₁ hv₂,
    sphericalWhittaker_smul_unipotent_mul_torus hϖ hθa _ X a hv₁, norm_mul, norm_zpow]
  set D := (openCellDepth hϖ Y).toNat with hD
  have hDz : openCellDepth hϖ Y = (D : ℤ) :=
    (Int.toNat_of_nonneg (openCellDepth_nonneg hϖ Y)).symm
  have hlsum : ∑ i, (μ₁ + lam) i = ∑ i, μ₁ i + D := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [← hDz]
    rfl
  have hnsum : ∑ j, (μ₂ + nu) j = ∑ j, μ₂ j - D := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [hnu, sum_openCellExponent_natAdd, hDz]
    ring
  have hlabs : ∑ i, ((μ₁ + lam) i).natAbs ≤ ∑ i, (μ₁ i).natAbs + D := by
    refine (natAbs_sum_add_le μ₁ lam).trans (Nat.add_le_add_left (le_of_eq ?_) _)
    have h := sum_natAbs_of_nonneg (fun i => openCellExponent_castAdd_nonneg hϖ Y i)
    rw [← hlam] at h
    have h2 : ∑ i, lam i = (D : ℤ) := by rw [← hDz]; rfl
    have h3 : ((∑ i, (lam i).natAbs : ℕ) : ℤ) = (D : ℤ) := by rw [h]; exact h2
    exact_mod_cast h3
  have hnabs : ∑ j, ((μ₂ + nu) j).natAbs ≤ ∑ j, (μ₂ j).natAbs + D := by
    refine (natAbs_sum_add_le μ₂ nu).trans (Nat.add_le_add_left (le_of_eq ?_) _)
    have h := sum_natAbs_of_nonpos (fun j => openCellExponent_natAdd_nonpos hϖ Y j)
    rw [← hnu] at h
    have h2 : ∑ j, nu j = -(D : ℤ) := by rw [hnu, sum_openCellExponent_natAdd, hDz]
    have h3 : ((∑ j, (nu j).natAbs : ℕ) : ℤ) = (D : ℤ) := by
      rw [h, show (∑ j, nu j) = -(D : ℤ) from h2, neg_neg]
    exact_mod_cast h3
  have hWa' := (hWa _ hv₁ (μ₁ + lam)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hRa hlabs) hCa)
  have hWc' := (hWc _ hv₂ (μ₂ + nu)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hRc hnabs) hCc)
  set σ' : ℝ := 1 / 2 + s.re / ((r + t + 2 : ℕ) : ℝ) with hσ'
  have hexp : (((((r + 1 : ℕ) : ℤ) * ∑ j, (μ₂ + nu) j - ((t + 1 : ℕ) : ℤ) *
      ∑ i, (μ₁ + lam) i : ℤ) : ℝ) * σ') =
      (((((r + 1 : ℕ) : ℤ) * ∑ j, μ₂ j - ((t + 1 : ℕ) : ℤ) * ∑ i, μ₁ i : ℤ) : ℝ) * σ') +
        (-((r + t + 2 : ℕ) : ℝ) * σ') * (D : ℝ) := by
    rw [hlsum, hnsum]
    push_cast
    ring
  rw [hexp, Real.rpow_add hq, Real.rpow_mul_natCast hq.le, hlsum, zpow_add₀ hX0, zpow_natCast]
  have hA : (0 : ℝ) ≤ (K.canonicalTopologicalData.residueCardinality : ℝ) ^
      (((((r + 1 : ℕ) : ℤ) * ∑ j, μ₂ j - ((t + 1 : ℕ) : ℤ) * ∑ i, μ₁ i : ℤ) : ℝ) * σ') :=
    Real.rpow_nonneg hq.le _
  have hB : (0 : ℝ) ≤ (K.canonicalTopologicalData.residueCardinality : ℝ) ^
      (-((r + t + 2 : ℕ) : ℝ) * σ') := Real.rpow_nonneg hq.le _
  have hXz : (0 : ℝ) ≤ ‖(X : ℂ)‖ ^ (∑ i, μ₁ i) := zpow_nonneg (norm_nonneg _) _
  calc _ ≤ (K.canonicalTopologicalData.residueCardinality : ℝ) ^
          (((((r + 1 : ℕ) : ℤ) * ∑ j, μ₂ j - ((t + 1 : ℕ) : ℤ) * ∑ i, μ₁ i : ℤ) : ℝ) * σ') *
        ((K.canonicalTopologicalData.residueCardinality : ℝ) ^
          (-((r + t + 2 : ℕ) : ℝ) * σ')) ^ D *
        (‖(X : ℂ)‖ ^ (∑ i, μ₁ i) * ‖(X : ℂ)‖ ^ D *
          (Ca * Ra ^ (∑ i, (μ₁ i).natAbs + D))) *
        (Cc * Rc ^ (∑ j, (μ₂ j).natAbs + D)) := by
        gcongr
    _ = _ := by
        rw [pow_add, pow_add, mul_pow, mul_pow, mul_pow]
        ring

include hϖ in
/-- A lattice-periodic function with values `≤ C ρ^D` (`C, ρ ≥ 0`) on the classes of depth `D` is
integrable when `q^((t+1)(r+1)) ρ < 1`. -/
theorem integrable_of_isLatticePeriodic_of_depth_bound
    {G : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier → ℂ} (hG : IsLatticePeriodic K G)
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hlt : (K.canonicalTopologicalData.residueCardinality : ℝ) ^ ((t + 1) * (r + 1)) * ρ < 1)
    (hb : ∀ Y, ‖G Y‖ ≤ C * ρ ^ (openCellDepth hϖ Y).toNat) :
    Integrable G (matrixHaar K (t + 1) (r + 1)) := by
  set q := K.canonicalTopologicalData.residueCardinality with hqdef
  have hshellS : ∀ D, ({y | classDepth K hϖ y = D} :
      Set (Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸ integralMatrices K (t + 1) (r + 1))).Finite ∧
      ({y | classDepth K hϖ y = D} :
        Set (Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸
          integralMatrices K (t + 1) (r + 1))).ncard ≤ q ^ ((t + 1) * (r + 1) * D) := by
    intro D
    apply finite_and_ncard_le K hϖ (t + 1) (r + 1)
    intro y hy i j
    have hD : openCellDepth hϖ (Quotient.out y) = (D : ℤ) := by
      rw [← hy, classDepth, Int.toNat_of_nonneg (openCellDepth_nonneg hϖ _)]
    have h := uniformizer_pow_depth_mul_mem hϖ (Quotient.out y) i j
    rwa [hD] at h
  have hs := summable_of_depth_bound (fun y => ((‖G (Quotient.out y)‖ : ℝ) : ℂ))
    (classDepth K hϖ) hC hρ (fun D => (hshellS D).1) (fun D => (hshellS D).2)
    (fun y => by
      rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      exact hb (Quotient.out y)) ?_
  · exact (integrable_and_hasSum_of_isLatticePeriodic K hG (Complex.summable_ofReal.1 hs)).1
  · have hg : Summable fun D : ℕ => C * ((q : ℝ) ^ ((t + 1) * (r + 1)) * ρ) ^ D :=
      (summable_geometric_of_lt_one (by positivity) hlt).mul_left C
    convert hg using 2 with D
    push_cast
    rw [mul_pow, ← pow_mul]
    ring

/-- Every torus point of `GL_((r+1)+(t+1))` is an exchanged block torus point. -/
theorem torus_eq_swapRank_blockSum (μ : Fin ((r + 1) + (t + 1)) → ℤ) :
    Iwasawa.torus ϖ μ = swapRank (r + 1) (t + 1) K.Carrier
      (blockSum (Iwasawa.torus ϖ (fun j : Fin (t + 1) =>
          μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) (j.castAdd (r + 1)))),
        Iwasawa.torus ϖ (fun i : Fin (r + 1) =>
          μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) (i.natAdd (t + 1)))))) := by
  rw [RankinSelberg.TwoBlockDominantRectangular.blockSum_torus]
  have key : ∀ k : Fin ((t + 1) + (r + 1)),
      Fin.append (fun j : Fin (t + 1) =>
          μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) (j.castAdd (r + 1))))
        (fun i : Fin (r + 1) => μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) (i.natAdd (t + 1)))) k =
        μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) k) := by
    intro k
    induction k using Fin.addCases with
    | left j => rw [Fin.append_left]
    | right i => rw [Fin.append_right]
  apply Units.ext
  ext i j
  change (Iwasawa.torus ϖ μ).val i j =
    (Iwasawa.torus ϖ (Fin.append (fun j : Fin (t + 1) =>
          μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) (j.castAdd (r + 1))))
        (fun i : Fin (r + 1) =>
          μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) (i.natAdd (t + 1)))))).val
      (Fin.cast (Nat.add_comm (r + 1) (t + 1)) i) (Fin.cast (Nat.add_comm (r + 1) (t + 1)) j)
  rw [torus_val, torus_val, Matrix.diagonal_apply, Matrix.diagonal_apply, key]
  have hcc : Fin.cast (Nat.add_comm (t + 1) (r + 1)) (Fin.cast (Nat.add_comm (r + 1) (t + 1)) i) = i :=
    Fin.ext rfl
  rw [hcc]
  by_cases hij : i = j
  · subst hij
    simp
  · have hij' : Fin.cast (Nat.add_comm (r + 1) (t + 1)) i ≠ Fin.cast (Nat.add_comm (r + 1) (t + 1)) j :=
      fun h => hij (Fin.ext (by simpa using congrArg Fin.val h))
    simp only [hij, hij', ite_false]

include hϖ in
/-- **Convergence at the torus points.** For `ψ` of conductor `𝒪` and fixed `(a, c, s)` there is `r₀ > 0` such that for
`‖X‖ < r₀` the Jacquet integrand of the section with parameters `(X a, c)` is integrable at
every torus point. -/
theorem exists_integrable_jacquetIntegrandAt_fullΦ
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ X : ℂˣ, ‖(X : ℂ)‖ < r₀ → ∀ μ : Fin ((r + 1) + (t + 1)) → ℤ,
      Integrable (jacquetIntegrandAt ψ hϖ (Base.fullΦ ψ hϖ (fun i => X * a i) c s)
        (Iwasawa.torus ϖ μ)) (matrixHaar K (t + 1) (r + 1)) := by
  set q := K.canonicalTopologicalData.residueCardinality with hqdef
  have hq : 1 ≤ q := K.canonicalTopologicalData.residueCardinality_gt_one.le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast residueCardinality_pos K
  have hθa := isIntegrallyTrivial_of_additiveConductor K hψ r
  have hθc := isIntegrallyTrivial_of_additiveConductor K hψ t
  obtain ⟨Ca, Ra, hCa, hRa, hWa⟩ := exists_norm_sphericalWhittaker_le hϖ hθa
    (fun w => Whittaker.norm_standardCharacter _ _ w) hq a
  obtain ⟨Cc, Rc, hCc, hRc, hWc⟩ := exists_norm_sphericalWhittaker_le hϖ hθc
    (fun w => Whittaker.norm_standardCharacter _ _ w) hq c
  set κ : ℝ := (q : ℝ) ^ (-((r + t + 2 : ℕ) : ℝ) * (1 / 2 + s.re / ((r + t + 2 : ℕ) : ℝ)))
    with hκ
  have hκ0 : 0 < κ := Real.rpow_pos_of_pos hq0 _
  have hQ : (0 : ℝ) < (q : ℝ) ^ ((t + 1) * (r + 1)) := by positivity
  have hRa0 : 0 < Ra := lt_of_lt_of_le one_pos hRa
  have hRc0 : 0 < Rc := lt_of_lt_of_le one_pos hRc
  refine ⟨1 / ((q : ℝ) ^ ((t + 1) * (r + 1)) * κ * Ra * Rc * 2), by positivity, ?_⟩
  intro X hX μ
  have hΦ := Base.isLeviInvariant_fullΦ hϖ hψ (fun i => X * a i) c s
  rw [torus_eq_swapRank_blockSum, jacquetIntegrandAt_swap ψ hϖ hΦ]
  set μ₂ : Fin (t + 1) → ℤ := fun j => μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) (j.castAdd (r + 1)))
  set μ₁ : Fin (r + 1) → ℤ := fun i => μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) (i.natAdd (t + 1)))
  have hb := norm_translatedLower_fullΦ_le ψ hϖ hψ a c s hCa hRa hCc hRc hWa hWc X μ₁ μ₂
  have hρ : (q : ℝ) ^ ((t + 1) * (r + 1)) * (κ * ‖(X : ℂ)‖ * Ra * Rc) < 1 := by
    have h1 : (q : ℝ) ^ ((t + 1) * (r + 1)) * κ * Ra * Rc * ‖(X : ℂ)‖ < 1 / 2 := by
      have hpos : 0 < (q : ℝ) ^ ((t + 1) * (r + 1)) * κ * Ra * Rc := by positivity
      have h2 := mul_lt_mul_of_pos_left hX hpos
      have h3 : (q : ℝ) ^ ((t + 1) * (r + 1)) * κ * Ra * Rc *
          (1 / ((q : ℝ) ^ ((t + 1) * (r + 1)) * κ * Ra * Rc * 2)) = 1 / 2 := by
        field_simp
      linarith
    nlinarith
  have hG := integrable_of_isLatticePeriodic_of_depth_bound hϖ
    (isLatticePeriodic_translatedLower hϖ hΦ (Iwasawa.torus ϖ μ₁) (Iwasawa.torus ϖ μ₂))
    (by positivity) (by positivity) hρ hb
  have hGc : Integrable (translatedLower hϖ (Base.fullΦ ψ hϖ (fun i => X * a i) c s)
      (Iwasawa.torus ϖ μ₁) (Iwasawa.torus ϖ μ₂) ∘
        rectangularConj (Iwasawa.torus ϖ μ₂) (Iwasawa.torus ϖ μ₁))
      (matrixHaar K (t + 1) (r + 1)) := by
    rw [← integrable_map_equiv, map_rectangularConj_padic K K.canonicalTopologicalData]
    exact hG.smul_measure_nnreal
  have hk : Continuous (intertwiningJacquetKernel r t ψ) := by
    have e : intertwiningJacquetKernel r t ψ =
        fun Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier => ψ.complex (-(Y (Fin.last t) 0)) :=
      funext (intertwiningJacquetKernel_eq_neg_corner ψ r t)
    rw [e]
    exact ψ.continuous_complex.comp (continuous_neg.comp
      ((continuous_apply 0).comp (continuous_apply (Fin.last t))))
  exact Integrable.bdd_mul (c := 1) hGc hk.aestronglyMeasurable
    (Filter.Eventually.of_forall fun Y => by
      rw [intertwiningJacquetKernel_eq_neg_corner, HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex])

end Translation

end Langlands.Shahidi.OpenCell
