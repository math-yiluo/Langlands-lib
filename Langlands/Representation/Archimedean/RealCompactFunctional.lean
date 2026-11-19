import Langlands.Representation.Archimedean.RealBlockFourierFinite
import Langlands.Representation.Archimedean.RealCompactRows

/-! # A functional on the real compact model -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealCompactFunctional

open Finset RealCompactRows RealBlockFourierFinite

variable {β γ : Type*} [DecidableEq β] [DecidableEq γ]

/-- Rotation acts with opposite weights on the two rows of its plane. -/
def rotationMode (b : β) : Rows β γ → ℤ
  | .inl (b', σ) => if b' = b then (if σ then 1 else -1) else 0
  | .inr _ => 0

/-- A diagonal gain is constant on each pair of rows. -/
def gain (a : β → ℂ) (d : γ → ℂ) : Rows β γ → ℂ
  | .inl (b, _) => a b
  | .inr c => d c

/-- The rotation matrix in the paired eigenbasis. -/
def rotation (b : β) (θ : ℝ) : Matrix (Rows β γ) (Rows β γ) ℂ :=
  Matrix.diagonal fun i => expMode (rotationMode b i) θ

variable [Fintype β] [Fintype γ]

/-- The permutation matrix that exchanges the two rows in each selected plane. -/
def flipMatrix (δ : β → Bool) : Matrix (Rows β γ) (Rows β γ) ℂ :=
  Matrix.permMatrixHom (R := ℂ) (flip δ)

theorem flipMatrix_eq_permMatrix (δ : β → Bool) :
    flipMatrix (γ := γ) δ = (flip δ).permMatrix ℂ := by
  simp [flipMatrix, Matrix.permMatrixHom, Equiv.Perm.inv_def]

theorem flipMatrix_mul (δ ε : β → Bool) :
    flipMatrix (γ := γ) δ * flipMatrix ε =
      flipMatrix (fun b => xor (δ b) (ε b)) := by
  rw [flipMatrix, flipMatrix, ← map_mul, flip_mul]
  rfl

/-- The prescribed scalar for a diagonal gain. -/
def gainScalar (w : β → ℕ) (s : γ → ℕ) (a : β → ℂ) (d : γ → ℂ) : ℂ :=
  (∏ b, a b ^ w b) * ∏ c, d c ^ s c

variable [LinearOrder (Rows β γ)]
variable (w : β → ℕ) (s : γ → ℕ)

/-- The underlying space of the tensor of compound matrix actions. -/
abbrev V := Configuration w s → ℂ

/-- The compound action with degrees taken from the prescribed row counts. -/
abbrev act : Matrix (Rows β γ) (Rows β γ) ℂ →* Module.End ℂ (V w s) :=
  CompoundMinorProduct.action (degree w s)

/-- The sign with a single negative coordinate. -/
def oneSign {α : Type*} [DecidableEq α] (i : α) (j : α) : ℂ :=
  if j = i then -1 else 1

/-- Invariance under exchanges of the two rows of a rotation plane. -/
def FlipInvariant (ℓ : V w s →ₗ[ℂ] ℂ) : Prop :=
  ∀ δ x, ℓ (act w s (flipMatrix δ) x) = ℓ x

/-- Covariance under diagonal gains with their prescribed scalar. -/
def GainCovariant (ℓ : V w s →ₗ[ℂ] ℂ) : Prop :=
  ∀ a d x, ℓ (act w s (Matrix.diagonal (gain a d)) x) = gainScalar w s a d * ℓ x

/-- The diagonal sign conditions on one pair or one singleton at a time. -/
def ElementaryGainCovariant (ℓ : V w s →ₗ[ℂ] ℂ) : Prop :=
  (∀ b x, ℓ (act w s (Matrix.diagonal (gain (oneSign b) 1)) x) = (-1 : ℂ) ^ w b * ℓ x) ∧
    ∀ c x, ℓ (act w s (Matrix.diagonal (gain 1 (oneSign c))) x) = (-1 : ℂ) ^ s c * ℓ x

/-- The Fourier coefficients strictly below `w b - 1` vanish along each rotation plane. -/
def FourierVanishing (ℓ : V w s →ₗ[ℂ] ℂ) : Prop :=
  ∀ b j, j.natAbs < w b - 1 → ∀ x, coeff j (fun θ => ℓ (act w s (rotation b θ) x)) = 0

variable {w s}

private abbrev basisVector (q : Configuration w s) : V w s :=
  Pi.single q 1

private def diagonalScalar (q : Configuration w s) (z : Rows β γ → ℂ) : ℂ :=
  ∏ a, z a ^ occurrence q a

omit [LinearOrder (Rows β γ)] in
private theorem diagonalScalar_eq (q : Configuration w s) (z : Rows β γ → ℂ) :
    (∏ t, ∏ a ∈ (q t).val, z a) = diagonalScalar q z := by
  have h (t : Fin (height w s)) :
      ∏ a ∈ (q t).val, z a = ∏ a, if a ∈ (q t).val then z a else 1 := by
    rw [← Finset.prod_filter]
    congr 1
    ext a
    simp
  simp only [h, diagonalScalar, occurrence, Finset.prod_comm (f := fun t a =>
    if a ∈ (q t).val then z a else 1)]
  exact prod_congr rfl fun a _ => by rw [← prod_filter, prod_const]

private theorem act_diagonal_basis (z : Rows β γ → ℂ) (q : Configuration w s) :
    act w s (Matrix.diagonal z) (basisVector q) = diagonalScalar q z • basisVector q := by
  rw [CompoundMinorProduct.action_diagonal, diagonalScalar_eq]

omit [LinearOrder (Rows β γ)] in
private theorem diagonalScalar_gain (q : Configuration w s) (a : β → ℂ) (d : γ → ℂ) :
    diagonalScalar q (gain a d) =
      (∏ b, a b ^ (occurrence q (.inl (b, true)) + occurrence q (.inl (b, false)))) *
        ∏ c, d c ^ occurrence q (.inr c) := by
  rw [diagonalScalar, Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp [gain, pow_add, mul_comm]

omit [LinearOrder (Rows β γ)] in
private theorem diagonalScalar_gain_target (ε : β → Bool) (a : β → ℂ) (d : γ → ℂ) :
    diagonalScalar (target w s ε) (gain a d) = gainScalar w s a d := by
  rw [diagonalScalar_gain, gainScalar]
  congr 1
  · apply prod_congr rfl
    intro b _
    cases h : ε b <;> simp [occurrence_target, count, h]
  · simp [occurrence_target, count]

theorem prod_oneSign_pow {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℕ) (i : α) :
    ∏ j, oneSign i j ^ p j = (-1 : ℂ) ^ p i := by
  rw [prod_eq_single_of_mem i (mem_univ i)]
  · simp [oneSign]
  · intro j _ hji
    simp [oneSign, hji]

omit [LinearOrder (Rows β γ)] in
private theorem diagonalScalar_pairSign (q : Configuration w s) (b : β) :
    diagonalScalar q (gain (oneSign b) 1) =
      (-1 : ℂ) ^ (occurrence q (.inl (b, true)) + occurrence q (.inl (b, false))) := by
  simp [diagonalScalar_gain, prod_oneSign_pow]

omit [LinearOrder (Rows β γ)] in
private theorem diagonalScalar_singletonSign (q : Configuration w s) (c : γ) :
    diagonalScalar q (gain 1 (oneSign c)) = (-1 : ℂ) ^ occurrence q (.inr c) := by
  simp [diagonalScalar_gain, prod_oneSign_pow]

private theorem expMode_pow (k : ℤ) (n : ℕ) (θ : ℝ) :
    expMode k θ ^ n = expMode ((n : ℤ) * k) θ := by
  rw [expMode, ← Complex.exp_nat_mul, expMode]
  congr 1
  push_cast
  ring

private theorem act_rotation_basis (b : β) (θ : ℝ) (q : Configuration w s) :
    act w s (rotation b θ) (basisVector q) = expMode (frequency q b) θ • basisVector q := by
  rw [rotation, act_diagonal_basis, diagonalScalar, Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [rotationMode, expMode_zero_left, one_pow, prod_const_one, mul_one]
  rw [prod_eq_single_of_mem b (mem_univ b)]
  · apply congrArg (fun z : ℂ => z • basisVector q)
    simp [expMode_pow]
    rw [← Pi.mul_apply, expMode_add]
    exact congrArg (fun k : ℤ => expMode k θ) (by unfold frequency; ring)
  · intro b' _ hb'
    simp [hb', expMode_zero_left]

private theorem coeff_rotation_basis (ℓ : V w s →ₗ[ℂ] ℂ) (b : β) (j : ℤ)
    (q : Configuration w s) :
    coeff j (fun θ => ℓ (act w s (rotation b θ) (basisVector q))) =
      ℓ (basisVector q) * (if frequency q b = j then 2 * (Real.pi : ℂ) else 0) := by
  have heq : (fun θ => ℓ (act w s (rotation b θ) (basisVector q))) =
      ℓ (basisVector q) • expMode (frequency q b) := by
    funext θ
    rw [act_rotation_basis, map_smul]
    simp [smul_eq_mul, mul_comm]
  rw [heq, coeff_smul, coeff_expMode]

private theorem neg_one_pow_pair (x y : ℕ) :
    (-1 : ℂ) ^ (x + y) = (-1 : ℂ) ^ (((x : ℤ) - y).natAbs) := by
  rw [neg_one_pow_eq_pow_mod_two (x + y), neg_one_pow_eq_pow_mod_two (((x : ℤ) - y).natAbs)]
  congr 1
  omega

/-- The elementary sign and Fourier conditions force support on the canonical configurations. -/
private theorem exists_target_of_ne_zero (hw : ∀ b, 0 < w b) (hs : ∀ c, s c ≤ 1)
    {ℓ : V w s →ₗ[ℂ] ℂ} (hg : ElementaryGainCovariant w s ℓ) (hf : FourierVanishing w s ℓ)
    {q : Configuration w s} (hq : ℓ (basisVector q) ≠ 0) :
    ∃ ε, q = target w s ε := by
  apply exists_eq_target q
  · intro b
    have hlow : w b - 1 ≤ (frequency q b).natAbs := by
      by_contra! hlt
      have h := hf b (frequency q b) hlt (basisVector q)
      rw [coeff_rotation_basis, ite_eq_left rfl] at h
      exact mul_ne_zero hq (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) h
    have hsign := hg.1 b (basisVector q)
    rw [act_diagonal_basis, diagonalScalar_pairSign, map_smul, smul_eq_mul] at hsign
    have hp := mul_right_cancel₀ hq hsign
    rw [neg_one_pow_pair] at hp
    change (-1 : ℂ) ^ (frequency q b).natAbs = (-1 : ℂ) ^ w b at hp
    by_contra! hlt
    have he : w b = (frequency q b).natAbs + 1 := by
      have := hw b
      omega
    have h₁ : (-1 : ℂ) ^ (frequency q b).natAbs = (-1 : ℂ) ^ (frequency q b).natAbs * (-1) :=
      hp.trans (by rw [he, pow_succ])
    have h₂ : (1 : ℂ) = -1 :=
      mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (by simpa using h₁)
    norm_num at h₂
  · intro c
    by_contra! hlt
    have hsign := hg.2 c (basisVector q)
    rw [act_diagonal_basis, diagonalScalar_singletonSign, map_smul, smul_eq_mul] at hsign
    have hp := mul_right_cancel₀ hq hsign
    have h₁ : s c = 1 := by
      have := hs c
      omega
    have h₀ : occurrence q (.inr c) = 0 := by omega
    norm_num [h₀, h₁] at hp

omit [LinearOrder (Rows β γ)] in
private theorem apply_eq_sum (ℓ : V w s →ₗ[ℂ] ℂ) (x : V w s) :
    ℓ x = ∑ q, x q * ℓ (basisVector q) := by
  calc
    ℓ x = ℓ (∑ q, Pi.single q (x q)) :=
      congrArg ℓ (LinearMap.sum_single_apply (fun _ : Configuration w s => ℂ) x).symm
    _ = _ := by
      rw [map_sum]
      apply sum_congr rfl
      intro q _
      have he : Pi.single q (x q) = x q • basisVector q := by
        change Pi.single q (x q) = x q • Pi.single q 1
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [he, map_smul, smul_eq_mul]

private theorem gainCovariant_of_support {ℓ : V w s →ₗ[ℂ] ℂ}
    (hℓ : ∀ q, ℓ (basisVector q) ≠ 0 → ∃ ε, q = target w s ε) :
    GainCovariant w s ℓ := by
  intro a d x
  change (ℓ.comp (act w s (Matrix.diagonal (gain a d)))) x = _
  rw [apply_eq_sum _ x, apply_eq_sum ℓ x, mul_sum]
  apply sum_congr rfl
  intro q _
  rw [LinearMap.comp_apply, act_diagonal_basis, map_smul, smul_eq_mul]
  by_cases hq : ℓ (basisVector q) = 0
  · simp [hq]
  · obtain ⟨ε, rfl⟩ := hℓ q hq
    rw [diagonalScalar_gain_target]
    ring

private theorem fourierVanishing_of_support {ℓ : V w s →ₗ[ℂ] ℂ}
    (hℓ : ∀ q, ℓ (basisVector q) ≠ 0 → ∃ ε, q = target w s ε) :
    FourierVanishing w s ℓ := by
  intro b j hj x
  have he (θ : ℝ) : ℓ (act w s (rotation b θ) x) =
      ∑ q, ((x q * ℓ (basisVector q)) • expMode (frequency q b)) θ := by
    change (ℓ.comp (act w s (rotation b θ))) x = _
    rw [apply_eq_sum _ x]
    apply sum_congr rfl
    intro q _
    rw [LinearMap.comp_apply, act_rotation_basis, map_smul, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul]
    ring
  simp only [coeff, he, sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_eq_zero
    intro q _
    change coeff j ((x q * ℓ (basisVector q)) • expMode (frequency q b)) = 0
    rw [coeff_smul, coeff_expMode]
    by_cases hq : ℓ (basisVector q) = 0
    · simp [hq]
    · obtain ⟨ε, rfl⟩ := hℓ q hq
      have hfreq : (frequency (target w s ε) b).natAbs = w b := by
        rw [frequency_target]
        cases ε b <;> simp
      have hne : frequency (target w s ε) b ≠ j := by
        intro heq
        rw [heq] at hfreq
        omega
      simp [hne]
  · intro q _
    exact intervalIntegrable_coeff ((continuous_expMode _).const_smul _) j _ _

omit [DecidableEq β] [DecidableEq γ] [LinearOrder (Rows β γ)] in
private theorem reindex_flip_target (δ ε : β → Bool) :
    CompoundMinorProduct.reindex (flip δ) (target w s ε) =
      target w s (fun b => if δ b then !(ε b) else ε b) :=
  funext fun t => Subtype.ext (targetRows_map_flip w s δ ε t)

private theorem exists_act_flip_basis (δ : β → Bool) (q : Configuration w s) :
    ∃ a : ℂ, a ≠ 0 ∧ act w s (flipMatrix δ) (basisVector q) =
      a • basisVector (CompoundMinorProduct.reindex (flip δ) q) :=
  CompoundMinorProduct.exists_action_perm_single (flip δ) q

private abbrev base (w : β → ℕ) (s : γ → ℕ) : Configuration w s :=
  target w s (fun _ => true)

/-- Sum the evaluations at the base configuration after applying each row exchange. -/
private def functional (w : β → ℕ) (s : γ → ℕ) : V w s →ₗ[ℂ] ℂ :=
  ∑ δ : β → Bool, (LinearMap.proj (base w s)).comp (act w s (flipMatrix δ))

private theorem functional_apply (x : V w s) :
    functional w s x = ∑ δ : β → Bool, act w s (flipMatrix δ) x (base w s) := by
  simp [functional, LinearMap.sum_apply]

private def xorRight (ε : β → Bool) : Equiv.Perm (β → Bool) :=
  Function.Involutive.toPerm (fun δ b => xor (δ b) (ε b)) (by
    intro δ
    funext b
    change xor (xor (δ b) (ε b)) (ε b) = δ b
    cases δ b <;> cases ε b <;> rfl)

private theorem functional_flipInvariant : FlipInvariant w s (functional w s) := by
  intro ε x
  simp only [functional_apply, ← Module.End.mul_apply, ← map_mul, flipMatrix_mul]
  exact Equiv.sum_comp (xorRight ε) (fun δ => act w s (flipMatrix δ) x (base w s))

private theorem functional_support (q : Configuration w s)
    (hq : functional w s (basisVector q) ≠ 0) :
    ∃ ε, q = target w s ε := by
  by_contra h
  apply hq
  rw [functional_apply]
  apply sum_eq_zero
  intro δ _
  obtain ⟨a, _, ha⟩ := exists_act_flip_basis δ q
  have hne : base w s ≠ CompoundMinorProduct.reindex (flip δ) q := by
    intro he
    have he' := congrArg (CompoundMinorProduct.reindex (degree := degree w s) (flip δ)).symm he
    rw [Equiv.symm_apply_apply, CompoundMinorProduct.reindex_symm, flip_symm,
      reindex_flip_target] at he'
    exact h ⟨_, he'.symm⟩
  simp only [ha, Pi.smul_apply, basisVector, Pi.single_eq_of_ne hne, smul_zero]

omit [LinearOrder (Rows β γ)] in
private theorem flipMatrix_false : flipMatrix (γ := γ) (fun _ : β => false) = 1 := by
  have he : flip (γ := γ) (fun _ : β => false) = 1 := by
    ext i
    rcases i with ⟨b, σ⟩ | c <;> rfl
  rw [flipMatrix, he, map_one]

private theorem functional_base (hw : ∀ b, 0 < w b) :
    functional w s (basisVector (base w s)) = 1 := by
  rw [functional_apply, sum_eq_single_of_mem (fun _ => false) (mem_univ _)]
  · simp only [flipMatrix_false, map_one, Module.End.one_apply, basisVector, Pi.single_eq_same]
  · intro δ _ hδ
    obtain ⟨a, _, ha⟩ := exists_act_flip_basis δ (base w s)
    have hne : base w s ≠ CompoundMinorProduct.reindex (flip δ) (base w s) := by
      intro he
      have he' := target_injective hw (he.trans (reindex_flip_target δ (fun _ => true)))
      apply hδ
      funext b
      have hb := congrFun he' b
      change true = (if δ b then !true else true) at hb
      cases h : δ b
      · rfl
      · simp [h] at hb
    simp only [ha, Pi.smul_apply, basisVector, Pi.single_eq_of_ne hne, smul_zero]

private theorem eq_smul_functional (hw : ∀ b, 0 < w b) (hs : ∀ c, s c ≤ 1)
    {ℓ : V w s →ₗ[ℂ] ℂ} (hp : FlipInvariant w s ℓ) (hg : ElementaryGainCovariant w s ℓ)
    (hf : FourierVanishing w s ℓ) :
    ℓ = ℓ (basisVector (base w s)) • functional w s := by
  apply LinearMap.ext
  intro x
  rw [apply_eq_sum ℓ x, apply_eq_sum (_ • _) x]
  apply sum_congr rfl
  intro q _
  rw [LinearMap.smul_apply, smul_eq_mul]
  by_cases hq : ∃ ε, q = target w s ε
  · obtain ⟨ε, rfl⟩ := hq
    let δ (b : β) : Bool := Bool.not (ε b)
    have hd : CompoundMinorProduct.reindex (flip δ) (base w s) = target w s ε := by
      rw [reindex_flip_target]
      congr 1
      funext b
      change (if Bool.not (ε b) = true then false else true) = ε b
      cases ε b <;> rfl
    obtain ⟨a, ha, he⟩ := exists_act_flip_basis δ (base w s)
    rw [hd] at he
    have hl := hp δ (basisVector (base w s))
    have hw' := functional_flipInvariant (w := w) (s := s) δ (basisVector (base w s))
    rw [he, map_smul, smul_eq_mul] at hl
    rw [he, map_smul, smul_eq_mul, functional_base hw] at hw'
    congr 1
    apply mul_left_cancel₀ ha
    calc
      a * ℓ (basisVector (target w s ε)) = ℓ (basisVector (base w s)) := hl
      _ = ℓ (basisVector (base w s)) * (a * functional w s (basisVector (target w s ε))) := by
        rw [hw', mul_one]
      _ = _ := by ring
  · have hl : ℓ (basisVector q) = 0 := by
      by_contra h
      exact hq (exists_target_of_ne_zero hw hs hg hf h)
    have hw' : functional w s (basisVector q) = 0 := by
      by_contra h
      exact hq (functional_support q h)
    simp [hl, hw']

/-- The sign and low-frequency conditions characterize the constructed functional up to scalar. -/
theorem exists_functional (w : β → ℕ) (s : γ → ℕ) (hw : ∀ b, 0 < w b) (hs : ∀ c, s c ≤ 1) :
    ∃ ω : V w s →ₗ[ℂ] ℂ, ω ≠ 0 ∧ FlipInvariant w s ω ∧ GainCovariant w s ω ∧
      FourierVanishing w s ω ∧
      ∀ ℓ : V w s →ₗ[ℂ] ℂ, FlipInvariant w s ℓ → ElementaryGainCovariant w s ℓ →
        FourierVanishing w s ℓ → ∃ c : ℂ, ℓ = c • ω := by
  refine ⟨functional w s, ?_, functional_flipInvariant, gainCovariant_of_support functional_support,
    fourierVanishing_of_support functional_support, ?_⟩
  · intro h
    simpa [h] using functional_base (s := s) hw
  · intro ℓ hp hg hf
    exact ⟨_, eq_smul_functional hw hs hp hg hf⟩

end Langlands.Archimedean.RealCompactFunctional
