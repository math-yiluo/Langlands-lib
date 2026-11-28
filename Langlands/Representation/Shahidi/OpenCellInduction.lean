import Langlands.Representation.Shahidi.OpenCellInductionAlgebra

/-! # The shell identities at `s = 0` for all ranks

Let `ψ` have conductor `𝒪`. The shell identities at `s = 0` hold for a first block of rank one. If they hold for the ranks
`(0, d)` and `(d, t)`, they hold for `(d + 1, t)`: for small nonzero `X` and `Z`, the two
generating series of the three-block coefficients give
`∏_j (1 - X a₁ a'_j⁻¹ q⁻¹) ∑_D P_D(X) Z^D = ∏_j (1 - X a₁ a'_j⁻¹ q⁻¹) ∑_D T_D(X) Z^D`, where `P_D(X)`
is the degree-`D` shell sum and `T_D(X)` the degree-`D` coefficient of the product, for the
first parameters `(X a₁, a')`; uniqueness of power series in `Z` gives `P_D(X) = T_D(X)` for small
`X`, and both sides are Laurent polynomials in `X`, so they agree at `X = 1`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocIndTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocIndValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocIndLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocIndT2Space : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocIndSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocIndMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocIndBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

section Laurent

variable {d : ℕ} (a₁ : Fin (0 + 1) → ℂˣ) (a' : Fin (d + 1) → ℂˣ)

theorem isPolynomialFn_append (i : Fin ((0 + 1) + (d + 1))) :
    IsPolynomialFn fun X : ℂˣ =>
      ((Fin.append (m := 0 + 1) (n := d + 1) (fun j => X * a₁ j) a' i : ℂˣ) : ℂ) := by
  induction i using Fin.addCases with
  | left j =>
    exact (isPolynomialFn_id.mul (isPolynomialFn_const (a₁ j : ℂ))).congr fun X => by simp
  | right j => exact (isPolynomialFn_const (a' j : ℂ)).congr fun X => by simp

theorem prod_append_val (X : ℂˣ) :
    ∏ i, ((Fin.append (m := 0 + 1) (n := d + 1) (fun j => X * a₁ j) a' i : ℂˣ) : ℂ) =
      (X : ℂ) * ((a₁ 0 : ℂ) * ∏ j, (a' j : ℂ)) := by
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, Units.val_mul, Fin.prod_univ_succ, Fin.prod_univ_zero,
    mul_one]
  ring

theorem isLaurentFn_satakeSchur_append (lam : Fin (0 + 1 + d + 1) → ℤ) :
    IsLaurentFn fun X : ℂˣ => GeneralLinear.Spherical.satakeSchur (n := 0 + 1 + d)
      (Fin.append (m := 0 + 1) (n := d + 1) (fun j => X * a₁ j) a') lam := by
  have h : IsLaurentFn fun X : ℂˣ => (X : ℂ) ^ lam (Fin.last (0 + 1 + d)) *
      ((a₁ 0 : ℂ) * ∏ j, (a' j : ℂ)) ^ lam (Fin.last (0 + 1 + d)) *
      MvPolynomial.eval (fun i : Fin (0 + 1 + d + 1) =>
        ((Fin.append (m := 0 + 1) (n := d + 1) (fun j => X * a₁ j) a' i : ℂˣ) : ℂ))
        (GeneralLinear.Spherical.jacobiTrudi ℂ fun i => lam i - lam (Fin.last (0 + 1 + d))) :=
    ((isLaurentFn_zpow _).mul (isLaurentFn_const _)).mul
      (isPolynomialFn_mvEval (σ := Fin (0 + 1 + d + 1)) _
        (x := fun i X => ((Fin.append (m := 0 + 1) (n := d + 1) (fun j => X * a₁ j) a' i : ℂˣ) : ℂ))
        (fun i => isPolynomialFn_append a₁ a' i)).isLaurentFn
  refine h.congr fun X => ?_
  unfold GeneralLinear.Spherical.satakeSchur
  erw [prod_append_val a₁ a' X]
  rw [mul_zpow (X : ℂ) ((a₁ 0 : ℂ) * ∏ j, (a' j : ℂ))]

theorem isLaurentFn_sphericalWhittaker_append {θ : upperUnipotent (0 + 1 + d + 1) K.Carrier →* ℂˣ}
    (q : ℕ) (g : Langlands.GeneralLinear (0 + 1 + d + 1) K.Carrier) :
    IsLaurentFn fun X : ℂˣ => GeneralLinear.Spherical.sphericalWhittaker (n := 0 + 1 + d) hϖ θ q
      (Fin.append (m := 0 + 1) (n := d + 1) (fun j => X * a₁ j) a') g := by
  unfold GeneralLinear.Spherical.sphericalWhittaker Iwasawa.cellFunction
  split_ifs
  · exact (isLaurentFn_const _).mul ((isLaurentFn_const _).mul (isLaurentFn_satakeSchur_append a₁ a' _))
  · exact isLaurentFn_const 0

variable {t : ℕ} (c : Fin (t + 1) → ℂˣ)

/-- The first diagonal block of the lift's chosen decomposition. -/
def liftPoint₁ {r t : ℕ} (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    Langlands.GeneralLinear (r + 1) K.Carrier :=
  liftFirst K r t ⟨(exists_liftShape_parabolic_mul r t hϖ x).choose,
    (exists_liftShape_parabolic_mul r t hϖ x).choose_spec.1⟩

/-- The second diagonal block of the lift's chosen decomposition. -/
def liftPoint₂ {r t : ℕ} (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    Langlands.GeneralLinear (t + 1) K.Carrier :=
  liftSecond K r t ⟨(exists_liftShape_parabolic_mul r t hϖ x).choose,
    (exists_liftShape_parabolic_mul r t hϖ x).choose_spec.1⟩

theorem liftFunction_eq_liftPoint {r t : ℕ}
    (Φ : Langlands.GeneralLinear (r + 1) K.Carrier → Langlands.GeneralLinear (t + 1) K.Carrier → ℂ)
    (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    liftFunction hϖ Φ x = Φ (liftPoint₁ hϖ x) (liftPoint₂ hϖ x) := rfl

theorem isLaurentFn_shellSum (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (D : ℤ) :
    IsLaurentFn fun X : ℂˣ => jacquetFunction ψ hϖ (degreePiece hϖ D (Base.fullΦ (r := 0 + 1 + d)
      (t := t) ψ hϖ (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0)) 1 := by
  have h : IsLaurentFn fun X : ℂˣ => ∑ y ∈ shellFinset (r := 0 + 1 + d) (t := t) hϖ D,
      intertwiningJacquetKernel (0 + 1 + d) t ψ (Quotient.out y) *
        (((twoBlockModulus K (liftPoint₁ (r := 0 + 1 + d) (t := t) hϖ
            (lower (0 + 1 + d + 1) (t + 1) K.Carrier (Quotient.out y)))
          (liftPoint₂ (r := 0 + 1 + d) (t := t) hϖ
            (lower (0 + 1 + d + 1) (t + 1) K.Carrier (Quotient.out y))) : ℝ) : ℂ) ^
            ((1 : ℂ) / 2 + 0 / ((0 + 1 + d + t + 2 : ℕ) : ℂ)) *
          GeneralLinear.Spherical.sphericalWhittaker (n := 0 + 1 + d) hϖ
            (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ (0 + 1 + d))
            K.canonicalTopologicalData.residueCardinality
            (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a')
            (liftPoint₁ (r := 0 + 1 + d) (t := t) hϖ
              (lower (0 + 1 + d + 1) (t + 1) K.Carrier (Quotient.out y))) *
          GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
            (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
            K.canonicalTopologicalData.residueCardinality c
            (liftPoint₂ (r := 0 + 1 + d) (t := t) hϖ
              (lower (0 + 1 + d + 1) (t + 1) K.Carrier (Quotient.out y)))) :=
    isLaurentFn_sum _ fun y _ => (isLaurentFn_const _).mul
      (((isLaurentFn_const _).mul (isLaurentFn_sphericalWhittaker_append hϖ a₁ a' _ _)).mul
        (isLaurentFn_const _))
  refine h.congr fun X => ?_
  rw [(hasSum_jacquetFunction_degreePiece_one ψ hϖ hψ
    (Base.isLeviInvariant_fullΦ hϖ hψ _ c 0) D).2]
  rfl

theorem isPolynomialFn_shellCoefficient (q : ℕ) (D : ℕ) :
    IsPolynomialFn fun X : ℂˣ => shellCoefficient (pairParameter (r := 0 + 1 + d) (t := t) q
      (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0) D := by
  unfold shellCoefficient
  refine isPolynomialFn_sum _ fun T _ => isPolynomialFn_prod _ fun x _ => ?_
  exact ((((isPolynomialFn_append a₁ a' x.1).mul (isPolynomialFn_const ((c x.2 : ℂ))⁻¹)).mul
    (isPolynomialFn_const ((q : ℂ) ^ (-(1 + (0 : ℂ)))))).neg).congr fun X => rfl

end Laurent

section Step

/-- **The induction step**, for `ψ` of conductor `𝒪`. -/
theorem coreAt_step (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) {d t : ℕ}
    (hA : CoreAt ψ hϖ 0 d) (hB : CoreAt ψ hϖ d t) : CoreAt ψ hϖ (0 + 1 + d) t := by
  intro a c D
  set q := K.canonicalTopologicalData.residueCardinality with hq
  set a₁ : Fin (0 + 1) → ℂˣ := fun i => a (Fin.castAdd (d + 1) i) with ha₁
  set a' : Fin (d + 1) → ℂˣ := fun j => a (Fin.natAdd (0 + 1) j) with ha'
  have ha : a = Fin.append (m := 0 + 1) (n := d + 1) (fun i => (1 : ℂˣ) * a₁ i) a' := by
    funext i
    refine Fin.addCases (m := 0 + 1) (n := d + 1) (motive := fun i => a i = Fin.append
      (m := 0 + 1) (n := d + 1) (fun i => (1 : ℂˣ) * a₁ i) a' i) (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left, one_mul]
    · rw [Fin.append_right]
  obtain ⟨r₀, hr₀, hL⟩ := threeCoef_series_left ψ hϖ d t a₁ a' c hψ hA
  choose ρ hρ hR using fun e₁ : ℕ => threeCoef_series_right ψ hϖ d t a₁ a' c hψ hB e₁
  have hne : (Finset.range (d + 1 + t + 1 + 1)).Nonempty := ⟨0, Finset.mem_range.2 (by omega)⟩
  set ρ₀ := (Finset.range (d + 1 + t + 1 + 1)).inf' hne ρ with hρ₀def
  have hρ₀ : 0 < ρ₀ := (Finset.lt_inf'_iff hne).2 fun e _ => hρ e
  set M : ℝ := 1 + ∑ x, ‖pairParameter q a₁ a' 0 x‖ with hMdef
  have hM : 0 < M := by positivity
  have hsmall : ∀ X : ℂˣ, X ∈ {X : ℂˣ | ‖(X : ℂ)‖ < min r₀ (1 / M)} →
      jacquetFunction ψ hϖ (degreePiece hϖ D (Base.fullΦ (r := 0 + 1 + d) (t := t) ψ hϖ
        (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0)) 1 =
      shellCoefficient (pairParameter (r := 0 + 1 + d) (t := t) q
        (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0) D := by
    intro X hX
    have hX' : ‖(X : ℂ)‖ < min r₀ (1 / M) := hX
    have hX₀ : ‖(X : ℂ)‖ < r₀ := lt_of_lt_of_le hX' (min_le_left _ _)
    have hXM : ‖(X : ℂ)‖ * M < 1 := by
      have := mul_lt_mul_of_pos_right (lt_of_lt_of_le hX' (min_le_right _ _)) hM
      rwa [one_div, inv_mul_cancel₀ hM.ne'] at this
    set Pr := ∏ x, (1 - (X : ℂ) * pairParameter q a₁ a' 0 x) with hPrdef
    have hPr : Pr ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro x _ h
      have h1 : (X : ℂ) * pairParameter q a₁ a' 0 x = 1 := by linear_combination -h
      have h2 : ‖pairParameter q a₁ a' 0 x‖ ≤ M := by
        have := Finset.single_le_sum (fun y _ => norm_nonneg (pairParameter q a₁ a' 0 y))
          (Finset.mem_univ x)
        linarith
      have h3 := congrArg norm h1
      rw [norm_mul, norm_one] at h3
      nlinarith [norm_nonneg (X : ℂ), norm_nonneg (pairParameter q a₁ a' 0 x)]
    have hfin : ∀ D' : ℤ, ∑ e₁ ∈ Finset.range (d + 1 + t + 1 + 1),
        (X : ℂ) ^ e₁ * threeCoef ψ hϖ d t a₁ a' c D' e₁ =
          Pr * jacquetFunction ψ hϖ (degreePiece hϖ D' (Base.fullΦ (r := 0 + 1 + d) (t := t) ψ hϖ
            (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0)) 1 := by
      intro D'
      have h := hL X hX₀ D'
      have hz : ∀ e ∉ (Finset.range (d + 1 + t + 1 + 1)).map Nat.castEmbedding,
          (X : ℂ) ^ e * threeCoef ψ hϖ d t a₁ a' c D' e = 0 := by
        intro e he
        rcases lt_or_ge e 0 with h0 | h0
        · rw [threeCoef_of_neg_right ψ hϖ d t a₁ a' c hψ D' h0, mul_zero]
        · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
          have hn : d + 1 + t + 1 + 1 ≤ n := by
            by_contra hlt
            exact he (Finset.mem_map.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)
          rw [threeCoef_of_lt ψ hϖ d t a₁ a' c hψ D' (by omega), mul_zero]
      have h2 : HasSum (fun e : ℤ => (X : ℂ) ^ e * threeCoef ψ hϖ d t a₁ a' c D' e)
          (∑ e ∈ (Finset.range (d + 1 + t + 1 + 1)).map Nat.castEmbedding,
            (X : ℂ) ^ e * threeCoef ψ hϖ d t a₁ a' c D' e) :=
        hasSum_sum_of_ne_finset_zero hz
      rw [h.unique h2, Finset.sum_map]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [Nat.castEmbedding_apply, zpow_natCast]
    have hcoef : (fun D' : ℕ => Pr * jacquetFunction ψ hϖ (degreePiece hϖ D'
        (Base.fullΦ (r := 0 + 1 + d) (t := t) ψ hϖ
          (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0)) 1) =
        (fun D' : ℕ => Pr * shellCoefficient (pairParameter (r := 0 + 1 + d) (t := t) q
          (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0) D') := by
      apply eq_of_hasSum_pow hρ₀
      intro z hz0 hz
      set Z : ℂˣ := Units.mk0 z hz0 with hZdef
      have hZval : (Z : ℂ) = z := rfl
      refine ⟨Pr * ∏ x, (1 - z * pairParameter (r := 0 + 1 + d) (t := t) q
          (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0 x), ?_, ?_⟩
      · have hS1 := hasSum_sum (s := Finset.range (d + 1 + t + 1 + 1)) fun e₁ he₁ =>
          (hR e₁ Z (by rw [hZval]; exact lt_of_lt_of_le hz (Finset.inf'_le _ he₁))).mul_left
            ((X : ℂ) ^ e₁)
        rw [sum_threeBlock_identity] at hS1
        rw [← hZval]
        convert hS1 using 1
        funext D'
        rw [← hfin (D' : ℤ), Finset.sum_mul]
        refine Finset.sum_congr rfl fun e₁ _ => ?_
        ring
      · have h := (hasSum_pow_mul_shellCoefficient z (pairParameter (r := 0 + 1 + d) (t := t) q
          (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0)).mul_left Pr
        convert h using 1
        funext D'
        ring
    exact mul_left_cancel₀ hPr (congrFun hcoef D)
  have heq := (isLaurentFn_shellSum ψ hϖ a₁ a' c hψ D).eq_of_infinite
    (isPolynomialFn_shellCoefficient a₁ a' c q D).isLaurentFn
    (infinite_small_units (lt_min hr₀ (by positivity))) hsmall 1
  rw [← ha] at heq
  exact heq

end Step

section AllRanks

theorem coreAt_zero (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (t : ℕ) :
    CoreAt ψ hϖ 0 t := by
  intro a c D
  have hf : IsOpenCellSection K ψ hϖ a c 0 (liftFunction hϖ (Base.fullΦ ψ hϖ a c 0)) :=
    fun X m₁ m₂ k hk => liftFunction_law hϖ (Base.isLeviInvariant_fullΦ hϖ hψ a c 0) X m₁ m₂ k hk
  exact (shellIdentity_iff ψ hϖ hψ hf).1 (Base.shellIdentity_rankOne hϖ hψ hf) D

/-- **The shell identities at `s = 0` hold for all ranks**, for `ψ` of conductor `𝒪`. -/
theorem coreAt_all (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (r t : ℕ) :
    CoreAt ψ hϖ r t := by
  induction r generalizing t with
  | zero => exact coreAt_zero ψ hϖ hψ t
  | succ d ih =>
    have h := coreAt_step ψ hϖ hψ (coreAt_zero ψ hϖ hψ d) (ih t)
    rwa [show 0 + 1 + d = d + 1 by omega] at h

end AllRanks

end Langlands.Shahidi.OpenCell
