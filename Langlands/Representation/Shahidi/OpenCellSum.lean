import Langlands.Representation.Shahidi.OpenCellBounds
import Langlands.Representation.Shahidi.OpenCellCount

/-! # Summation by depth -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

section Generic

variable {Q : Type*} (F : Q → ℂ) (depth : Q → ℕ)

/-- A family whose depth fibers are finite, with at most `N D` elements of depth `D` and
values bounded by `C ρ ^ D`, is summable when `∑ N D C ρ^D` converges. -/
theorem summable_of_depth_bound {C ρ : ℝ} {N : ℕ → ℕ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hfin : ∀ D, {y | depth y = D}.Finite) (hcount : ∀ D, {y | depth y = D}.ncard ≤ N D)
    (hbound : ∀ y, ‖F y‖ ≤ C * ρ ^ depth y)
    (hgeom : Summable fun D => (N D : ℝ) * (C * ρ ^ D)) : Summable F := by
  apply Summable.of_norm
  let e := Equiv.sigmaFiberEquiv depth
  rw [← e.summable_iff]
  have hnn : ∀ x, 0 ≤ ((fun y => ‖F y‖) ∘ e) x := fun x => norm_nonneg _
  rw [summable_sigma_of_nonneg hnn]
  have hfinT : ∀ D, Finite {y // depth y = D} := fun D => (hfin D).to_subtype
  constructor
  · intro D
    exact Summable.of_finite
  · refine Summable.of_nonneg_of_le (fun D => tsum_nonneg fun y => hnn _) (fun D => ?_) hgeom
    have := hfinT D
    let _ := Fintype.ofFinite {y // depth y = D}
    rw [tsum_fintype]
    calc ∑ y : {y // depth y = D}, ((fun y => ‖F y‖) ∘ e) ⟨D, y⟩
        ≤ ∑ _y : {y // depth y = D}, C * ρ ^ D := by
          apply Finset.sum_le_sum
          intro y _
          have h := hbound y.1
          rw [y.2] at h
          exact h
      _ = (Fintype.card {y // depth y = D} : ℝ) * (C * ρ ^ D) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (N D : ℝ) * (C * ρ ^ D) := by
          have h0 : 0 ≤ C * ρ ^ D := mul_nonneg hC (pow_nonneg hρ D)
          apply mul_le_mul_of_nonneg_right _ h0
          have hc : Fintype.card {y // depth y = D} = {y | depth y = D}.ncard := by
            rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
            rfl
          exact_mod_cast hc ▸ hcount D

/-- If the depth fibers have sums `g D` and `g` has sum `P`, the summable family has sum `P`. -/
theorem hasSum_of_depth_fibers {g : ℕ → ℂ} {P : ℂ} (hg : HasSum g P)
    (hfib : ∀ D, HasSum (fun y : {y // depth y = D} => F y) (g D)) (hF : Summable F) :
    HasSum F P := by
  let e := Equiv.sigmaFiberEquiv depth
  rw [← e.hasSum_iff]
  exact HasSum.sigma_of_hasSum hg (fun D => hfib D) (e.summable_iff.2 hF)

end Generic

section Padic

open Langlands.GeneralLinear Langlands.GeneralLinear.Spherical Langlands.Conductor

universe u

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance ocSumTopologicalSpace : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance ocSumValuativeRel : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance ocSumIsNonarchimedeanLocalField : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField

variable {r t : ℕ}
  {ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _ K.canonicalTopologicalData.topology}
  {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
  {a : Fin (r + 1) → ℂˣ} {c : Fin (t + 1) → ℂˣ} {s : ℂ}
  {f : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ}

/-- The summand of the open-cell sum at a matrix `Y`. -/
def openCellSummand (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
      K.canonicalTopologicalData.topology)
    (f : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) : ℂ :=
  f (blockWeyl (r + 1) (t + 1) K.Carrier * intertwiningUnipotent (r + 1) (t + 1) K.Carrier Y) *
    starRingEnd ℂ (ψ (Y (Fin.last t) 0) : ℂ)

/-- `max(1, q^A)`, a bound at least `1` for parameters of norm at most `q^A`. -/
def paramBound (q : ℕ) (A : ℝ) : ℝ := max 1 ((q : ℝ) ^ A)

/-- The constant of the summand bound. -/
def summandConstant (q : ℕ) (r t : ℕ) (A B : ℝ) : ℝ :=
  ((r + 1).factorial : ℝ) * (2 ^ (2 * (r + 1)) * paramBound q A ^ (r + 1)) ^ (r + 1) *
    (((t + 1).factorial : ℝ) * (2 ^ (2 * (t + 1)) * paramBound q B ^ (t + 1)) ^ (t + 1))

/-- The ratio of the summand bound. -/
def summandRatio (q : ℕ) (r t : ℕ) (A B : ℝ) (s : ℂ) : ℝ :=
  (q : ℝ) ^ (-s.re) * ((q : ℝ) ^ (r + t) * ((2 ^ (r + 1) * paramBound q A ^ (2 * (r + 1))) *
    (2 ^ (t + 1) * paramBound q B ^ (2 * (t + 1)))))

theorem paramBound_one_le (q : ℕ) (A : ℝ) : 1 ≤ paramBound q A := le_max_left _ _

theorem le_paramBound (q : ℕ) (A : ℝ) : (q : ℝ) ^ A ≤ paramBound q A := le_max_right _ _

/-- For `q ≥ 1` and `N > 0`, `‖(q^(-N D))^(1/2 + s/N)‖ ≤ (q^(-Re s))^D`. -/
theorem norm_modulus_cpow_le {q : ℕ} (hq : 1 ≤ q) {N : ℕ} (hN : 0 < N) (D : ℕ) (s : ℂ) :
    ‖((((q : ℝ) ^ (-((N : ℤ) * (D : ℤ))) : ℝ)) : ℂ) ^ ((1 : ℂ) / 2 + s / (N : ℂ))‖ ≤
      ((q : ℝ) ^ (-s.re)) ^ D := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (zpow_pos hq0 _)]
  have hre : ((1 : ℂ) / 2 + s / (N : ℂ)).re = 1 / 2 + s.re / N := by
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    simp [Complex.div_re, Complex.normSq_natCast]
    field_simp
  rw [hre, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
  apply Real.rpow_le_rpow_of_exponent_le hq1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  push_cast
  rw [mul_add]
  have : -((N : ℝ) * D) * (s.re / N) = -(D * s.re) := by
    field_simp
  rw [this]
  nlinarith [show (0 : ℝ) ≤ N * D by positivity]

theorem isIntegrallyTrivial_of_additiveConductor
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (n : ℕ) :
    Iwasawa.IsIntegrallyTrivial
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel)
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ n) :=
  GeneralLinear.Iwasawa.isIntegrallyTrivial_standardCharacter
    (RankinSelberg.HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero K ψ hψ).1 n

/-- **The bound for the summand.** For `ψ` of conductor `𝒪`, a section with the target
transformation law and `‖a_i‖ ≤ q^A`, `‖c_j⁻¹‖ ≤ q^B`: `|F(Y)| ≤ C ρ ^ D` with `D` the depth of `Y`. -/
theorem norm_openCellSummand_le (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (hf : IsOpenCellSection K ψ hϖ a c s f) {A B : ℝ}
    (ha : ∀ i, ‖(a i : ℂ)‖ ≤ (K.canonicalTopologicalData.residueCardinality : ℝ) ^ A)
    (hc : ∀ j, ‖((c j)⁻¹ : ℂ)‖ ≤ (K.canonicalTopologicalData.residueCardinality : ℝ) ^ B)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    ‖openCellSummand K ψ f Y‖ ≤
      summandConstant K.canonicalTopologicalData.residueCardinality r t A B *
        summandRatio K.canonicalTopologicalData.residueCardinality r t A B s ^
          (openCellDepth hϖ Y).toNat := by
  set q := K.canonicalTopologicalData.residueCardinality with hqdef
  have hq : 1 ≤ q := K.canonicalTopologicalData.residueCardinality_gt_one.le
  have hq0 : (0 : ℝ) ≤ q := by positivity
  obtain ⟨u₁, hu₁, u₂, hu₂, hval⟩ := exists_openCellSection_value K hϖ hf Y
  set Dn := (openCellDepth hϖ Y).toNat with hDn
  have hDz : openCellDepth hϖ Y = (Dn : ℤ) := (Int.toNat_of_nonneg (openCellDepth_nonneg hϖ Y)).symm
  unfold openCellSummand
  rw [blockWeyl_mul_intertwiningUnipotent, hval _ (blockWeyl_mem_integralSubgroup K r t),
    norm_mul, Complex.norm_conj, Circle.norm_coe, mul_one, norm_mul, norm_mul, hDz]
  have hmod := norm_modulus_cpow_le hq (N := r + t + 2) (by omega) Dn s
  have hθa := isIntegrallyTrivial_of_additiveConductor K hψ r
  have hθc := isIntegrallyTrivial_of_additiveConductor K hψ t
  have hWa := norm_sphericalWhittaker_le_of_nonneg hϖ hθa (fun w => Whittaker.norm_standardCharacter _ _ w)
    hq a (paramBound_one_le q A) (fun i => (ha i).trans (le_paramBound q A)) hu₁
    (fun i => openCellExponent_castAdd_nonneg hϖ Y i) (D := Dn) (by rw [← hDz]; rfl)
  have hWc := norm_sphericalWhittaker_le_of_nonpos hϖ hθc
    (fun w => Whittaker.norm_standardCharacter _ _ w)
    hq c (paramBound_one_le q B) (fun j => (hc j).trans (le_paramBound q B)) hu₂
    (fun j => openCellExponent_natAdd_nonpos hϖ Y j) (D := Dn)
    (by rw [sum_openCellExponent_natAdd, hDz])
  calc _ ≤ ((q : ℝ) ^ (-s.re)) ^ Dn *
        ((q : ℝ) ^ (r * Dn) * (((r + 1).factorial : ℝ) *
          (2 ^ (2 * (r + 1)) * paramBound q A ^ (r + 1)) ^ (r + 1) *
          (2 ^ (r + 1) * paramBound q A ^ (2 * (r + 1))) ^ Dn)) *
        ((q : ℝ) ^ (t * Dn) * (((t + 1).factorial : ℝ) *
          (2 ^ (2 * (t + 1)) * paramBound q B ^ (t + 1)) ^ (t + 1) *
          (2 ^ (t + 1) * paramBound q B ^ (2 * (t + 1))) ^ Dn)) := by
        have h0 : (0 : ℝ) ≤ ((q : ℝ) ^ (-s.re)) ^ Dn := by positivity
        exact mul_le_mul (mul_le_mul hmod hWa (norm_nonneg _) h0) hWc (norm_nonneg _)
          (mul_nonneg h0 ((norm_nonneg _).trans hWa))
    _ = _ := by
        rw [summandConstant, summandRatio]
        generalize (2 : ℝ) = b
        ring

end Padic

end Langlands.Shahidi.OpenCell
