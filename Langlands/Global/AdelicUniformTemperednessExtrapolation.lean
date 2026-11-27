import Langlands.Global.AdelicUniformTemperednessTorusFrame
import Langlands.Global.AdelicEisensteinUnitaryExponentStatement
import Langlands.Global.AdelicHalfModulusRootProductStatement
import Langlands.Global.AdelicSiegelMeasureReduction
import Langlands.Analysis.ShiftRecurrenceBound
import Langlands.Global.AdelicExponentPolynomials

/-! # Extrapolation of constant terms along dominant split-component directions

A function satisfying subunitary shift equations of order `m` along `𝔄_J` is bounded at
`x₁ w`, for a dominant positive point `x₁` of `T` on which the roots in `J` are trivial, by
`3^m (m ‖x₁‖ + 3)^m δ_T(x₁)^{1/2}` times its supremum near `w`. Here `δ_T` is the product of
the positive roots with their multiplicities. -/

noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {𝓕 : StandardParabolicFamily F G}

local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν

variable (𝓕) in
/-- The modulus `δ_T(x) = ∏_{β ∈ Φ⁺} |β(x)|^{m_β}` on `T(𝔸)`. -/
def torusModulus (x : AdelicGroupPoints F 𝓕.T.toGrp) : ℝ :=
  ∏ᶠ (β : characterLattice 𝓕.T) (_ : β ∈ positiveRelativeRoots 𝓕.i 𝓕.ν),
    ((normCharacter F 𝓕.T β x : ℝ≥0) : ℝ) ^ Module.finrank F (weightSpace 𝓕.i β)

theorem log_normCharacter (x : AdelicGroupPoints F 𝓕.T.toGrp) (χ : characterLattice 𝓕.T) :
    Real.log ((normCharacter F 𝓕.T χ x : ℝ≥0) : ℝ) = characterLog F 𝓕.T.toGrp x χ := rfl

theorem coe_finprod_nnreal' {α : Sort*} (f : α → ℝ≥0) :
    ((∏ᶠ a, f a : ℝ≥0) : ℝ) = ∏ᶠ a, (f a : ℝ) := by
  simpa using MonoidHom.map_finprod_of_injective (NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom
    NNReal.coe_injective f

/-- The modulus is a product of positive powers of the simple roots. -/
theorem exists_torusModulus_eq [Fintype Δ] :
    ∃ e : Δ → ℕ, (∀ α, e α ≠ 0) ∧ ∀ x : AdelicGroupPoints F 𝓕.T.toGrp,
      torusModulus 𝓕 x = ∏ α : Δ, ((normCharacter F 𝓕.T α.val x : ℝ≥0) : ℝ) ^ e α := by
  obtain ⟨e, he, hx⟩ := AdelicSiegelFactors.exists_simpleRoot_exponents (G := G) 𝓕.i 𝓕.ν
    (𝟙 𝓕.T) 𝓕.isSplitTorus_T
  refine ⟨e, he, fun x => ?_⟩
  have h := congrArg (fun r : ℝ≥0 => (r : ℝ)) (hx x)
  simp only [Category.id_comp, NNReal.coe_prod, NNReal.coe_pow] at h
  rw [torusModulus, ← h, coe_finprod_nnreal']
  refine finprod_congr fun β => ?_
  rw [coe_finprod_nnreal']
  refine finprod_congr fun _ => ?_
  rw [NNReal.coe_pow]

theorem normCharacter_pos (x : AdelicGroupPoints F 𝓕.T.toGrp) (χ : characterLattice 𝓕.T) :
    (0 : ℝ) < ((normCharacter F 𝓕.T χ x : ℝ≥0) : ℝ) := by
  exact_mod_cast pos_iff_ne_zero.mpr (normCharacter F 𝓕.T χ x).ne_zero

theorem torusModulus_pos [Fintype Δ] (x : AdelicGroupPoints F 𝓕.T.toGrp) :
    0 < torusModulus 𝓕 x := by
  obtain ⟨e, -, he⟩ := exists_torusModulus_eq (𝓕 := 𝓕)
  rw [he]
  exact Finset.prod_pos fun α _ => pow_pos (normCharacter_pos x α.val) _

theorem torusModulus_mul [Fintype Δ] (x y : AdelicGroupPoints F 𝓕.T.toGrp) :
    torusModulus 𝓕 (x * y) = torusModulus 𝓕 x * torusModulus 𝓕 y := by
  obtain ⟨e, -, he⟩ := exists_torusModulus_eq (𝓕 := 𝓕)
  rw [he, he, he, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun α _ => ?_
  rw [map_mul, Units.val_mul, NNReal.coe_mul, mul_pow]

theorem torusModulus_pow [Fintype Δ] (x : AdelicGroupPoints F 𝓕.T.toGrp) (n : ℕ) :
    torusModulus 𝓕 (x ^ n) = torusModulus 𝓕 x ^ n := by
  induction n with
  | zero =>
    obtain ⟨e, -, he⟩ := exists_torusModulus_eq (𝓕 := 𝓕)
    simp only [pow_zero, he, map_one, Units.val_one, NNReal.coe_one, one_pow,
      Finset.prod_const_one]
  | succ n ih => rw [pow_succ, torusModulus_mul, ih, pow_succ]

/-- The logarithm of the modulus is a linear form in the root coordinates. -/
theorem log_torusModulus [Fintype Δ] (Fr : TorusFrame 𝓕) :
    ∃ e : Δ → ℕ, ∀ x : AdelicGroupPoints F 𝓕.T.toGrp,
      Real.log (torusModulus 𝓕 x) = ∑ α : Δ, (e α : ℝ) * (Fr.step α * (Fr.crd x).1 α) := by
  obtain ⟨e, -, he⟩ := exists_torusModulus_eq (𝓕 := 𝓕)
  refine ⟨e, fun x => ?_⟩
  rw [he, Real.log_prod (fun α _ => (pow_pos (normCharacter_pos x α.val) _).ne')]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Real.log_pow, log_normCharacter, Fr.characterLog_root]

/-- The modulus is at least one at a point whose root coordinates are nonnegative. -/
theorem one_le_torusModulus [Fintype Δ] (Fr : TorusFrame 𝓕) {x : AdelicGroupPoints F 𝓕.T.toGrp}
    (hx : ∀ α : Δ, 0 ≤ (Fr.crd x).1 α) : 1 ≤ torusModulus 𝓕 x := by
  obtain ⟨e, he⟩ := log_torusModulus Fr
  have hlog : 0 ≤ Real.log (torusModulus 𝓕 x) := by
    rw [he]
    exact Finset.sum_nonneg fun α _ =>
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Fr.step_pos α).le (hx α))
  have := Real.add_one_le_exp (Real.log (torusModulus 𝓕 x))
  rw [Real.exp_log (torusModulus_pos x)] at this
  linarith

/-- The image in `G(𝔸)` of a point of `T(𝔸)`. -/
abbrev torusPoint (x : AdelicGroupPoints F 𝓕.T.toGrp) : AdelicGroupPoints F G :=
  map F 𝓕.T.toGrp G 𝓕.i x

variable (𝓕) in
/-- `φ` satisfies **shift equations of order `m` along `J`** on the positive torus. Here `J` is
any set of characters of `T`. For every positive point `t` of `T` at which every character in
`J` takes the value `1` and every simple root has idele norm at least `1`, left translation by
the image of `t` satisfies `∏_{k<m} (L_t - w_k) φ = 0` with `|w_k| ≤ δ_T(t)^{1/2}`. In the
uniform temperedness criterion `J` is the set of simple roots of a standard index. -/
def HasTorusShiftEquations (J : Set (characterLattice 𝓕.T)) (m : ℕ)
    (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ t ∈ intrinsicSubgroup F 𝓕.T, (∀ β ∈ J, Lie.characterValue β t = 1) →
    (∀ α ∈ Δ, 1 ≤ normCharacter F 𝓕.T α t) →
    ∃ w : Fin m → ℂ, (∀ k, ‖w k‖ ≤ Real.sqrt (torusModulus 𝓕 t)) ∧
      IsTranslationPolynomialSolution (torusPoint t) (∏ k, (X - C (w k))) φ

/-- Given the half-modulus statement, subunitary shift equations along `𝔄_{J'}` give torus shift
equations along every set `J ⊇ J'` of characters of `T`. -/
theorem hasTorusShiftEquations_of_le (hHM : HalfModulusRootProductStatement.{0})
    {J' : StandardIndex F G 𝓕.i 𝓕.ν} {J : Set (characterLattice 𝓕.T)} (hJ : J'.1 ⊆ J)
    {m : ℕ} {φ : AdelicGroupPoints F G → ℂ} (h : 𝓕.HasSubunitaryShiftEquations J' m φ) :
    HasTorusShiftEquations 𝓕 J m φ := by
  intro t ht hJt hdom
  obtain ⟨s, hs⟩ := 𝓕.exists_splitPoint J' ht fun β hβ => hJt β (hJ hβ)
  have hdomS : 𝓕.IsDominantSplitPoint J' s := by
    intro α hα _
    rw [𝓕.normCharacter_splitPoint, hs]
    exact hdom α hα
  obtain ⟨w, hw, hsol⟩ := h s hdomS
  have hκ2 : ‖𝓕.halfModulus J' (positivePointMap F (𝓕.P J') (𝓕.A J') (𝓕.a J' ≫ 𝓕.l J') s)‖ ^ 2
      = torusModulus 𝓕 t := by
    rw [hHM F G 𝓕 J' s, torusModulus]
    refine finprod_congr fun β => finprod_congr fun _ => ?_
    rw [𝓕.normCharacter_splitPoint, hs]
  refine ⟨w, fun k => (hw k).trans (le_of_eq ?_), ?_⟩
  · rw [← hκ2, Real.sqrt_sq (norm_nonneg _)]
  · have hpt : map F (𝓕.P J') G (𝓕.p J')
        (positivePointMap F (𝓕.P J') (𝓕.A J') (𝓕.a J' ≫ 𝓕.l J') s) = torusPoint t := by
      rw [𝓕.map_p_positivePointMap, hs]
    rw [← hpt]
    exact hsol

/-- A difference of solutions solves the product equation. -/
theorem HasTorusShiftEquations.sub {J : Set (characterLattice 𝓕.T)} {m m' : ℕ}
    {φ ψ : AdelicGroupPoints F G → ℂ} (hφ : HasTorusShiftEquations 𝓕 J m φ)
    (hψ : HasTorusShiftEquations 𝓕 J m' ψ) : HasTorusShiftEquations 𝓕 J (m + m') (φ - ψ) := by
  intro t ht hJ hdom
  obtain ⟨w₁, hw₁, h₁⟩ := hφ t ht hJ hdom
  obtain ⟨w₂, hw₂, h₂⟩ := hψ t ht hJ hdom
  refine ⟨Fin.append w₁ w₂, fun k => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]; exact hw₁ i
    · rw [Fin.append_right]; exact hw₂ i
  · rw [isTranslationPolynomialSolution_iff_aeval] at h₁ h₂ ⊢
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have hφ' : aeval (Langlands.HarmonicAnalysis.GroupAction.leftFunctions (torusPoint t)⁻¹)
        ((∏ i : Fin m, (X - C (w₁ i))) * ∏ i : Fin m', (X - C (w₂ i))) φ = 0 := by
      rw [mul_comm, map_mul, Module.End.mul_apply, h₁, map_zero]
    have hψ' : aeval (Langlands.HarmonicAnalysis.GroupAction.leftFunctions (torusPoint t)⁻¹)
        ((∏ i : Fin m, (X - C (w₁ i))) * ∏ i : Fin m', (X - C (w₂ i))) ψ = 0 := by
      rw [map_mul, Module.End.mul_apply, h₂, map_zero]
    rw [map_sub, hφ', hψ', sub_zero]

/-- **Extrapolation along a dominant direction.** Let `J ⊆ Δ` be a set of simple roots, let `φ`
satisfy shift equations of order `m` along `J`, and let `x₁` and `w` be positive points of `T`,
the root coordinates of `x₁` being `0` on `J` and `≥ 0` elsewhere. Let `B ≥ 0`. If
`‖φ(u ω)‖ ≤ B` for every positive `u` whose coordinates are within `1` of those of `w`, then
`‖φ(x₁ w ω)‖ ≤ 3^m (m ‖x₁‖ + 3)^m δ_T(x₁)^{1/2} B`. -/
theorem norm_le_of_hasTorusShiftEquations [Fintype Δ] (Fr : TorusFrame 𝓕)
    {J : Set (characterLattice 𝓕.T)} (hJΔ : J ⊆ Δ) {m : ℕ} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : HasTorusShiftEquations 𝓕 J m φ) (ω : AdelicGroupPoints F G)
    {x₁ w : AdelicGroupPoints F 𝓕.T.toGrp} (hx₁ : x₁ ∈ intrinsicSubgroup F 𝓕.T)
    (hw : w ∈ intrinsicSubgroup F 𝓕.T)
    (hJ : ∀ β : Δ, β.val ∈ J → (Fr.crd x₁).1 β = 0) (hdom : ∀ α : Δ, 0 ≤ (Fr.crd x₁).1 α)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ intrinsicSubgroup F 𝓕.T, ‖Fr.crd u - Fr.crd w‖ ≤ 1 →
      ‖φ (torusPoint u * ω)‖ ≤ B) :
    ‖φ (torusPoint (x₁ * w) * ω)‖ ≤
      3 ^ m * ((m : ℝ) * ‖Fr.crd x₁‖ + 3) ^ m * Real.sqrt (torusModulus 𝓕 x₁) * B := by
  classical
  set N : ℕ := ⌈(m : ℝ) * ‖Fr.crd x₁‖⌉₊ + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos _
  have hNr : (m : ℝ) * ‖Fr.crd x₁‖ ≤ N := by
    have := Nat.le_ceil ((m : ℝ) * ‖Fr.crd x₁‖)
    rw [hNdef]
    push_cast
    linarith
  have hN1 : (N : ℝ) + 1 ≤ (m : ℝ) * ‖Fr.crd x₁‖ + 3 := by
    have h := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) (norm_nonneg (Fr.crd x₁)))
    rw [hNdef]
    push_cast
    linarith
  obtain ⟨σ, hσ, hσN, hσc⟩ := Fr.exists_pow_eq hx₁ hN
  have hσdom : ∀ α : Δ, 0 ≤ (Fr.crd σ).1 α := by
    intro α
    rw [hσc, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) (hdom α)
  have hσJ : ∀ β ∈ J, Lie.characterValue β σ = 1 := by
    intro β hβ
    refine Fr.characterValue_eq_one hσ (β := ⟨β, hJΔ hβ⟩) ?_
    rw [hσc, Prod.smul_fst, Pi.smul_apply, hJ ⟨β, hJΔ hβ⟩ hβ, smul_zero]
  have hσd : ∀ α ∈ Δ, 1 ≤ normCharacter F 𝓕.T α σ := by
    intro α hα
    have hlog : 0 ≤ Real.log ((normCharacter F 𝓕.T α σ : ℝ≥0) : ℝ) := by
      rw [log_normCharacter, Fr.characterLog_root σ ⟨α, hα⟩]
      exact mul_nonneg (Fr.step_pos _).le (hσdom _)
    have h1 : (1 : ℝ) ≤ ((normCharacter F 𝓕.T α σ : ℝ≥0) : ℝ) := by
      have := Real.add_one_le_exp (Real.log ((normCharacter F 𝓕.T α σ : ℝ≥0) : ℝ))
      rw [Real.exp_log (normCharacter_pos σ α)] at this
      linarith
    exact_mod_cast h1
  obtain ⟨wr, hwr, hsol⟩ := hφ σ hσ hσJ hσd
  set κ := Real.sqrt (torusModulus 𝓕 σ) with hκ
  have hκ1 : 1 ≤ κ := by
    rw [hκ, Real.one_le_sqrt]
    exact one_le_torusModulus Fr hσdom
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos hκ1
  have hapow : ∀ j : ℕ, torusPoint σ ^ j = torusPoint (σ ^ j) := fun j => (map_pow _ σ j).symm
  have hbase : ∀ j < m, ‖φ (torusPoint σ ^ j * (torusPoint w * ω))‖ ≤ κ ^ j * B := by
    intro j hj
    rw [hapow, ← mul_assoc, torusPoint, torusPoint, ← map_mul]
    have hu := hB (σ ^ j * w) (mul_mem (pow_mem hσ j) hw) (by
      rw [Fr.crd_mul, Fr.crd_pow, add_sub_cancel_right, hσc, smul_smul, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hjm : (j : ℝ) ≤ m := by exact_mod_cast hj.le
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      rw [← div_eq_mul_inv, div_mul_eq_mul_div, div_le_one hNpos]
      calc (j : ℝ) * ‖Fr.crd x₁‖ ≤ m * ‖Fr.crd x₁‖ := by gcongr
        _ ≤ N := hNr)
    calc _ ≤ B := hu
      _ ≤ κ ^ j * B := le_mul_of_one_le_left hB0 (one_le_pow₀ hκ1)
  have hmain := Langlands.Analysis.norm_le_of_translationSolution (torusPoint σ) wr hκpos hwr φ
    hsol (torusPoint w * ω) hB0 hbase N
  have hpt : torusPoint σ ^ N * (torusPoint w * ω) = torusPoint (x₁ * w) * ω := by
    rw [hapow, hσN, ← mul_assoc, torusPoint, torusPoint, torusPoint, map_mul]
  rw [hpt] at hmain
  have hκN : κ ^ N = Real.sqrt (torusModulus 𝓕 x₁) := by
    rw [hκ, ← hσN, torusModulus_pow]
    have ha := (torusModulus_pos (𝓕 := 𝓕) σ).le
    calc Real.sqrt (torusModulus 𝓕 σ) ^ N
        = Real.sqrt ((Real.sqrt (torusModulus 𝓕 σ) ^ N) ^ 2) :=
          (Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) N)).symm
      _ = Real.sqrt (torusModulus 𝓕 σ ^ N) := by
          rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt ha]
  rw [hκN] at hmain
  refine hmain.trans ?_
  have : ((N : ℝ) + 1) ^ m ≤ ((m : ℝ) * ‖Fr.crd x₁‖ + 3) ^ m :=
    pow_le_pow_left₀ (by positivity) hN1 m
  have hsq : 0 ≤ Real.sqrt (torusModulus 𝓕 x₁) := Real.sqrt_nonneg _
  gcongr

/-- The modulus is controlled exponentially by the coordinates, in both directions. -/
theorem exists_torusModulus_bounds [Fintype Δ] (Fr : TorusFrame 𝓕) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ y : AdelicGroupPoints F 𝓕.T.toGrp,
      Real.exp (-(Λ * ‖Fr.crd y‖)) ≤ torusModulus 𝓕 y ∧
        torusModulus 𝓕 y ≤ Real.exp (Λ * ‖Fr.crd y‖) := by
  obtain ⟨e, he⟩ := log_torusModulus Fr
  refine ⟨∑ α : Δ, (e α : ℝ) * Fr.step α,
    Finset.sum_nonneg fun α _ => mul_nonneg (Nat.cast_nonneg _) (Fr.step_pos α).le, fun y => ?_⟩
  have habs : |Real.log (torusModulus 𝓕 y)| ≤ (∑ α : Δ, (e α : ℝ) * Fr.step α) * ‖Fr.crd y‖ := by
    rw [he, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (Fr.step_pos α),
      mul_assoc (e α : ℝ)]
    have hc : |(Fr.crd y).1 α| ≤ ‖Fr.crd y‖ :=
      (norm_le_pi_norm (Fr.crd y).1 α).trans (norm_fst_le (Fr.crd y))
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc (Fr.step_pos α).le)
      (Nat.cast_nonneg _)
  have hpos := torusModulus_pos (𝓕 := 𝓕) y
  constructor
  · rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (Real.log (torusModulus 𝓕 y))])
  · rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith [le_abs_self (Real.log (torusModulus 𝓕 y))])

open Classical in
/-- **Bound at a chamber point.** Let `Λ ≥ 0` be such that `δ_T(y) ≥ e^{-Λ ‖y‖}` for every
`y ∈ T(𝔸)`, where `‖y‖` is the norm of the coordinates of `y`. Let `J ⊆ Δ` be a set of simple
roots and let `φ` satisfy shift equations of order `m` along `J`. Let `x` be a positive point of
`T` and `ρ, ρ' ≥ 0`, the root coordinates of `x` in `J` being at most `ρ` in absolute value and
all its root coordinates at least `-ρ'`. Let `B ≥ 0`, and suppose `‖φ(u ω)‖ ≤ B` at every
positive `u` whose coordinates in `J` are within `1` of those of `x`, whose other root
coordinates lie in `[-ρ' - 1, 1]` and whose central coordinates have norm at most `1`. Then
`‖φ(x ω)‖ ≤ 3^m (m ‖x‖ + 3)^m δ_T(x)^{1/2} e^{Λ(ρ + ρ' + 1)} B`. -/
theorem norm_le_of_hasTorusShiftEquations_chamber [Fintype Δ]
    (Fr : TorusFrame 𝓕) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ y : AdelicGroupPoints F 𝓕.T.toGrp,
      Real.exp (-(Λ * ‖Fr.crd y‖)) ≤ torusModulus 𝓕 y)
    {J : Set (characterLattice 𝓕.T)} (hJΔ : J ⊆ Δ) {m : ℕ} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : HasTorusShiftEquations 𝓕 J m φ)
    {x : AdelicGroupPoints F 𝓕.T.toGrp} (hx : x ∈ intrinsicSubgroup F 𝓕.T)
    (ω : AdelicGroupPoints F G) {ρ ρ' : ℝ} (hρ : 0 ≤ ρ) (hρ' : 0 ≤ ρ')
    (hJ : ∀ β : Δ, β.val ∈ J → |(Fr.crd x).1 β| ≤ ρ)
    (hD : ∀ α : Δ, -ρ' ≤ (Fr.crd x).1 α) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ intrinsicSubgroup F 𝓕.T,
      (∀ β : Δ, β.val ∈ J → |(Fr.crd u).1 β - (Fr.crd x).1 β| ≤ 1) →
      (∀ α : Δ, α.val ∉ J → -ρ' - 1 ≤ (Fr.crd u).1 α ∧ (Fr.crd u).1 α ≤ 1) →
      ‖(Fr.crd u).2‖ ≤ 1 → ‖φ (torusPoint u * ω)‖ ≤ B) :
    ‖φ (torusPoint x * ω)‖ ≤ 3 ^ m * ((m : ℝ) * ‖Fr.crd x‖ + 3) ^ m *
      Real.sqrt (torusModulus 𝓕 x) * (Real.exp (Λ * (ρ + ρ' + 1)) * B) := by
  obtain ⟨x₁, hx₁, x₀, hx₀, xc, hxc, hxeq, h₁, h₀, hc⟩ := Fr.exists_split J hx
  have hn₀ : ‖Fr.crd x₀‖ ≤ ρ' := by
    rw [h₀]
    refine (norm_prod_le_iff.mpr ⟨?_, ?_⟩)
    · refine (pi_norm_le_iff_of_nonneg hρ').mpr fun α => ?_
      dsimp only
      split_ifs
      · simpa using hρ'
      · rw [Real.norm_eq_abs, abs_of_nonpos (min_le_right _ _)]
        have := hD α
        rcases le_total ((Fr.crd x).1 α) 0 with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h]; linarith
    · simpa using hρ'
  have hnc : ‖Fr.crd xc‖ ≤ ρ := by
    rw [hc]
    refine (norm_prod_le_iff.mpr ⟨?_, ?_⟩)
    · refine (pi_norm_le_iff_of_nonneg hρ).mpr fun α => ?_
      dsimp only
      split_ifs with h
      · rw [Real.norm_eq_abs]; exact hJ α h
      · simpa using hρ
    · simpa using hρ
  have hn₁ : ‖Fr.crd x₁‖ ≤ ‖Fr.crd x‖ := by
    rw [h₁]
    refine norm_prod_le_iff.mpr ⟨?_, norm_snd_le (Fr.crd x)⟩
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun α => ?_
    refine le_trans ?_ ((norm_le_pi_norm (Fr.crd x).1 α).trans (norm_fst_le _))
    dsimp only
    split_ifs
    · simp
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)
  set w := x₀ * xc with hw
  have hwmem : w ∈ intrinsicSubgroup F 𝓕.T := mul_mem hx₀ hxc
  have hcw : Fr.crd w = (fun α => if α.val ∈ J then (Fr.crd x).1 α
      else min ((Fr.crd x).1 α) 0, 0) := by
    rw [hw, Fr.crd_mul, h₀, hc]
    refine Prod.ext (funext fun α => ?_) (by simp)
    simp only [Prod.fst_add, Pi.add_apply]
    split_ifs <;> simp
  have hJ₁ : ∀ β : Δ, β.val ∈ J → (Fr.crd x₁).1 β = 0 := by
    intro β hβ
    rw [h₁]
    simp [hβ]
  have hdom : ∀ α : Δ, 0 ≤ (Fr.crd x₁).1 α := by
    intro α
    rw [h₁]
    dsimp only
    split_ifs
    · exact le_rfl
    · exact le_max_right _ _
  have hBound : ∀ u ∈ intrinsicSubgroup F 𝓕.T, ‖Fr.crd u - Fr.crd w‖ ≤ 1 →
      ‖φ (torusPoint u * ω)‖ ≤ B := by
    intro u hu hdu
    have hcomp : ∀ α : Δ, |(Fr.crd u).1 α - (Fr.crd w).1 α| ≤ 1 := fun α =>
      ((norm_le_pi_norm ((Fr.crd u).1 - (Fr.crd w).1) α).trans
        (norm_fst_le (Fr.crd u - Fr.crd w))).trans hdu
    refine hB u hu (fun β hβ => ?_) (fun α hα => ?_) ?_
    · have := hcomp β
      rw [hcw] at this
      simpa [hβ] using this
    · have h1 := hcomp α
      rw [hcw] at h1
      simp only [hα, ite_false] at h1
      have hmin : -ρ' ≤ min ((Fr.crd x).1 α) 0 := le_min (hD α) (by linarith)
      have hmin' : min ((Fr.crd x).1 α) 0 ≤ 0 := min_le_right _ _
      rw [abs_le] at h1
      constructor <;> linarith [h1.1, h1.2]
    · have := (norm_snd_le (Fr.crd u - Fr.crd w)).trans hdu
      rw [hcw] at this
      simpa using this
  have hmain := norm_le_of_hasTorusShiftEquations Fr hJΔ hφ ω hx₁ hwmem hJ₁ hdom hB0 hBound
  have hxw : x = x₁ * w := by rw [hxeq, hw, mul_assoc]
  rw [← hxw] at hmain
  refine hmain.trans ?_
  have hnw : ‖Fr.crd w‖ ≤ ρ + ρ' := by
    rw [hw, Fr.crd_mul]
    linarith [norm_add_le (Fr.crd x₀) (Fr.crd xc)]
  have hmod : torusModulus 𝓕 x₁ ≤ torusModulus 𝓕 x * Real.exp (Λ * (ρ + ρ')) := by
    have hm := torusModulus_mul (𝓕 := 𝓕) x₁ w
    rw [← hxw] at hm
    have hlow := hΛ w
    have hwpos := torusModulus_pos (𝓕 := 𝓕) w
    have h1 : torusModulus 𝓕 x₁ = torusModulus 𝓕 x / torusModulus 𝓕 w := by
      rw [hm, mul_div_cancel_right₀ _ hwpos.ne']
    rw [h1, div_le_iff₀ hwpos]
    have : Real.exp (-(Λ * (ρ + ρ'))) ≤ torusModulus 𝓕 w :=
      le_trans (Real.exp_le_exp.mpr (by nlinarith)) hlow
    calc torusModulus 𝓕 x = torusModulus 𝓕 x * Real.exp (Λ * (ρ + ρ')) *
          Real.exp (-(Λ * (ρ + ρ'))) := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ _ := by
          gcongr
          exact (mul_pos (torusModulus_pos x) (Real.exp_pos _)).le
  have hsqrt : Real.sqrt (torusModulus 𝓕 x₁) ≤
      Real.sqrt (torusModulus 𝓕 x) * Real.exp (Λ * (ρ + ρ' + 1)) := by
    calc Real.sqrt (torusModulus 𝓕 x₁) ≤
          Real.sqrt (torusModulus 𝓕 x * Real.exp (Λ * (ρ + ρ'))) := Real.sqrt_le_sqrt hmod
      _ = Real.sqrt (torusModulus 𝓕 x) * Real.sqrt (Real.exp (Λ * (ρ + ρ'))) :=
          Real.sqrt_mul (torusModulus_pos x).le _
      _ ≤ Real.sqrt (torusModulus 𝓕 x) * Real.exp (Λ * (ρ + ρ' + 1)) := by
          gcongr
          refine Real.sqrt_le_iff.mpr ⟨(Real.exp_pos _).le, ?_⟩
          rw [← Real.exp_nat_mul]
          exact Real.exp_le_exp.mpr (by push_cast; nlinarith)
  have hpoly : ((m : ℝ) * ‖Fr.crd x₁‖ + 3) ^ m ≤ ((m : ℝ) * ‖Fr.crd x‖ + 3) ^ m := by
    gcongr
  calc 3 ^ m * ((m : ℝ) * ‖Fr.crd x₁‖ + 3) ^ m * Real.sqrt (torusModulus 𝓕 x₁) * B
      ≤ 3 ^ m * ((m : ℝ) * ‖Fr.crd x‖ + 3) ^ m *
          (Real.sqrt (torusModulus 𝓕 x) * Real.exp (Λ * (ρ + ρ' + 1))) * B := by
        gcongr
    _ = _ := by ring

end Langlands.Global.StandardParabolicFamily
