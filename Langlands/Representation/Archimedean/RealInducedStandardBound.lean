import Langlands.Representation.Archimedean.RealInducedTorusBound
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient

/-!
# The torus-pairing bound for real standard modules

Let `ds` be a list of real blocks of total rank `N`, `h` an `O(N)`-finite function of the
standard module `realStandardModule N ds` and `u` an `O(N)`-finite function of the dual principal
series `principalSeries ℝ N (dualChar (realPositionCharacter ds))`. Let `T` be the torus of the
rotations of the induction blocks of `ds`. This module applies the torus-pairing bound of
`RealInducedTorusBound` to `u` and `h`: there is `C` with

`|∫_T u(τ y_1) h(τ y_2) dτ| ≤ C |∫_T E_u(τ y_1) E_h(τ y_2) dτ|` for all `y_1, y_2`,

where `E_h` and `E_u` are the right `O(N)`-invariant functions of the principal series of
`|·|^{t_l}` and `|·|^{-t_l}`, `t_l` the real part of the exponent of the block containing the
position `l` (`exists_bound`, statement `RealInducedStandardBoundStatement`).
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

namespace RealInducedStandardBound

open RealBlockRotation RealBlockFourierFinite RealInducedBlockSlice RealInducedBlockBound
  RealInducedTorusCore RealInducedTorusBound PartialJacquet GramFormula PrincipalSeriesExtension
  RealStrictCharacterLanglandsQuotient

/-! ## Positions of the blocks -/

/-- The real part of the exponent of the block containing the position `p` (`0` past the end). -/
def realPositionBlockExponent : List RealBlock → ℕ → ℝ
  | [], _ => 0
  | .character d :: _, 0 => d.exponent.re
  | .character _ :: ds, p + 1 => realPositionBlockExponent ds p
  | .induced d :: _, 0 => d.exponent.re
  | .induced d :: _, 1 => d.exponent.re
  | .induced _ :: ds, p + 2 => realPositionBlockExponent ds p

/-- The characters, exponents and block exponents at an induction block with first position `p`;
the position `p + 1` is not the first position of an induction block. -/
theorem induced_at : ∀ {ds : List RealBlock} {p : ℕ} {d : ComplexCharacterData},
    realInducedBlockAt ds p = some d →
      realPositionCharacter ds p = realInducedFirstCharacter d ∧
      realPositionCharacter ds (p + 1) = realInducedSecondCharacter d ∧
      realPositionExponent ds p = d.exponent + (d.weight.natAbs : ℂ) / 2 ∧
      realPositionExponent ds (p + 1) = d.exponent - (d.weight.natAbs : ℂ) / 2 ∧
      realPositionBlockExponent ds p = d.exponent.re ∧
      realPositionBlockExponent ds (p + 1) = d.exponent.re ∧
      realInducedBlockAt ds (p + 1) = none
  | [], _, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: _, 0, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: ds, p + 1, _, h => by
      have := induced_at (ds := ds) (p := p) h
      simpa only [realPositionCharacter, realPositionExponent, realPositionBlockExponent,
        realInducedBlockAt] using this
  | .induced d :: _, 0, d', h => by
      simp only [realInducedBlockAt, Option.some.injEq] at h
      subst h
      simp [realPositionCharacter, realPositionExponent, realPositionBlockExponent,
        realInducedBlockAt]
  | .induced _ :: _, 1, _, h => by simp [realInducedBlockAt] at h
  | .induced _ :: ds, p + 2, _, h => by
      have := induced_at (ds := ds) (p := p) h
      simpa only [realPositionCharacter, realPositionExponent, realPositionBlockExponent,
        realInducedBlockAt] using this

/-- Away from the induction blocks, the exponent at a position has real part the block
exponent. -/
theorem exponent_re_eq : ∀ (ds : List RealBlock) (i : ℕ),
    (∀ p d, realInducedBlockAt ds p = some d → i ≠ p ∧ i ≠ p + 1) →
      (realPositionExponent ds i).re = realPositionBlockExponent ds i
  | [], _, _ => by simp [realPositionExponent, realPositionBlockExponent]
  | .character _ :: _, 0, _ => by simp [realPositionExponent, realPositionBlockExponent]
  | .character _ :: ds, i + 1, h => by
      simp only [realPositionExponent, realPositionBlockExponent]
      exact exponent_re_eq ds i fun p d hd => by
        have := h (p + 1) d (by simpa [realInducedBlockAt] using hd)
        omega
  | .induced d :: _, 0, h => absurd rfl (h 0 d (by simp [realInducedBlockAt])).1
  | .induced d :: _, 1, h => absurd rfl (h 0 d (by simp [realInducedBlockAt])).2
  | .induced _ :: ds, i + 2, h => by
      simp only [realPositionExponent, realPositionBlockExponent]
      exact exponent_re_eq ds i fun p d hd => by
        have := h (p + 2) d (by simpa [realInducedBlockAt] using hd)
        omega

/-! ## The slots of the induction blocks -/

variable {N : ℕ}

/-- The slot of the induction block `d` at the position `p`: covariance exponent
`α = e_p + (N - 1)/2 - p`, weight `|m|`, mode `0` and coordinates `0`. -/
def mkSlot (ds : List RealBlock) (N p : ℕ) (hp : p + 1 < N) (d : ComplexCharacterData) :
    Slot N where
  p := p
  hp := hp
  α := realPositionExponent ds p + ((N : ℂ) - 1) / 2 - (p : ℂ)
  M := d.weight.natAbs
  j := 0
  x := 0
  y := 0
  w := 0

/-- The slot at the position `p`, if an induction block starts there. -/
def slotAt (ds : List RealBlock) (N p : ℕ) : Option (Slot N) :=
  match realInducedBlockAt ds p with
  | none => none
  | some d => if hp : p + 1 < N then some (mkSlot ds N p hp d) else none

/-- The slots of all induction blocks of `ds`, in order. -/
def slots (ds : List RealBlock) (N : ℕ) : List (Slot N) :=
  (List.range N).filterMap (slotAt ds N)

theorem mem_slotAt {ds : List RealBlock} {p : ℕ} {s : Slot N} (h : s ∈ slotAt ds N p) :
    ∃ (d : ComplexCharacterData) (hp : p + 1 < N),
      realInducedBlockAt ds p = some d ∧ s = mkSlot ds N p hp d := by
  rw [Option.mem_def] at h
  unfold slotAt at h
  split at h
  · simp at h
  · rename_i d hd
    by_cases hp : p + 1 < N
    · simp only [hp, ↓reduceDIte, Option.some.injEq] at h
      exact ⟨d, hp, hd, h.symm⟩
    · simp [hp] at h

theorem mem_slots {ds : List RealBlock} {s : Slot N} (hs : s ∈ slots ds N) :
    ∃ (p : ℕ) (hp : p + 1 < N) (d : ComplexCharacterData),
      realInducedBlockAt ds p = some d ∧ s = mkSlot ds N p hp d := by
  obtain ⟨p, -, hp⟩ := List.mem_filterMap.mp hs
  obtain ⟨d, hp', hd, rfl⟩ := mem_slotAt (Option.mem_def.mpr hp)
  exact ⟨p, hp', d, hd, rfl⟩

theorem mkSlot_mem_slots {ds : List RealBlock} {p : ℕ} {d : ComplexCharacterData}
    (hd : realInducedBlockAt ds p = some d) (hp : p + 1 < N) : mkSlot ds N p hp d ∈ slots ds N := by
  refine List.mem_filterMap.mpr ⟨p, List.mem_range.mpr (by omega), ?_⟩
  unfold slotAt
  rw [hd]
  simp only [hp, ↓reduceDIte]

theorem pairwise_slots (ds : List RealBlock) (N : ℕ) : (slots ds N).Pairwise Slot.Disjoint := by
  unfold slots
  rw [List.pairwise_filterMap]
  refine List.pairwise_lt_range.imp fun {a b} hab s hs t ht => ?_
  obtain ⟨d, hpa, hda, rfl⟩ := mem_slotAt hs
  obtain ⟨d', hpb, hdb, rfl⟩ := mem_slotAt ht
  left
  show a + 1 < b
  have hnone := (induced_at hda).2.2.2.2.2.2
  by_contra hc
  have hb : b = a + 1 := by omega
  rw [hb, hnone] at hdb
  exact absurd hdb (by simp)

/-! ## Degrees -/

theorem hasDegree_mono {S : List (Slot N)} {D D' : ℕ} (h : D ≤ D')
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : HasDegree S D f) : HasDegree S D' f :=
  fun s hs j hj k hk => hf s hs j (lt_of_le_of_lt (by exact_mod_cast h) hj) k hk

theorem exists_hasDegree {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : Continuous f)
    (hK : IsKFin f) : ∀ S : List (Slot N), ∃ D : ℕ, HasDegree S D f
  | [] => ⟨0, fun s hs => by simp at hs⟩
  | s :: S => by
      obtain ⟨D1, hD1⟩ := exists_blockFourierCoefficient_eq_zero s.hp hf hK
      obtain ⟨D2, hD2⟩ := exists_hasDegree hf hK S
      refine ⟨max D1 D2, fun t ht j hj k hk => ?_⟩
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hD1 j (lt_of_le_of_lt (by exact_mod_cast le_max_left _ _) hj) k hk
      · exact hD2 t ht j (lt_of_le_of_lt (by exact_mod_cast le_max_right _ _) hj) k hk

/-! ## Exponential equivariance -/

theorem apply_exp {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (hχ : IsSignedPower χ e) (l : ℕ) (x : ℝ) :
    χ l (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') = Complex.exp (e l * x) := by
  have hs : signUnit (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') = 1 := by
    unfold signUnit
    exact ite_eq_left_iff.mpr fun h => absurd (Real.exp_pos x) h
  rw [hχ.eq, hs, hχ.one, one_mul, Units.val_mk0, abs_of_pos (Real.exp_pos x),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]

/-! ## Comparison functions -/

/-- The character `x ↦ |x|^{e_l}`. -/
def absChar (e : ℕ → ℝ) (l : ℕ) (x : ℝˣ) : ℂ := ((|(x : ℝ)| : ℝ) : ℂ) ^ ((e l : ℝ) : ℂ)

/-- The right `O(N)`-invariant function `b κ ↦ ∏_l |b_ll|^{e_l + (N - 1)/2 - l}` of the principal
series of `absChar e`. -/
def expFun (N : ℕ) (e : ℕ → ℝ) : Langlands.GeneralLinear N ℝ → ℂ :=
  extension (shiftedExponent N fun l => (e l : ℂ)) fun _ => 1

theorem absChar_signUnit (e : ℕ → ℝ) (l : ℕ) (x : ℝˣ) : absChar e l (signUnit x) = 1 := by
  simp [absChar, abs_signUnit]

theorem absChar_eq (e : ℕ → ℝ) (l : ℕ) (x : ℝˣ) :
    absChar e l x = absChar e l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ ((e l : ℝ) : ℂ) := by
  rw [absChar_signUnit, one_mul]
  rfl

theorem principalSeriesCharacter_absChar_sign (e : ℕ → ℝ) (a : Fin N → ℝˣ) :
    principalSeriesCharacter ℝ N (absChar e) (fun i => signUnit (a i)) = 1 := by
  unfold principalSeriesCharacter
  refine Finset.prod_eq_one fun i _ => ?_
  rw [absChar_signUnit, one_mul]
  have : ‖((signUnit (a i) : ℝˣ) : ℝ)‖ = 1 := by rw [Real.norm_eq_abs, abs_signUnit]
  rw [this]
  simp

theorem expFun_mem (N : ℕ) (e : ℕ → ℝ) : expFun N e ∈ principalSeries ℝ N (absChar e) := by
  refine extension_mem_principalSeries (χ := absChar e) (fun l => (e l : ℂ)) (absChar_eq e)
    continuous_const ?_ fun a κ => by rw [principalSeriesCharacter_absChar_sign, one_mul]
  have : (Set.range fun k : Matrix.unitaryGroup (Fin N) ℝ =>
      fun x : Matrix.unitaryGroup (Fin N) ℝ => (fun _ => (1 : ℂ)) (x * k)) =
      {fun _ => (1 : ℂ)} := Set.range_const
  rw [this]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _)

theorem contMDiff_expFun (N : ℕ) (e : ℕ → ℝ) :
    ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ (expFun N e) :=
  (expFun_mem N e).1

theorem isExpEquivariant_expFun (N : ℕ) (e : ℕ → ℝ) :
    RealBlockDerivative.IsExpEquivariant
      (fun i : Fin N => ((e i + ((N : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) : ℝ) : ℂ)) (expFun N e) := by
  have h := RealBlockDerivative.isExpEquivariant_of_mem_principalSeries
    (τ := fun i : Fin N => ((e i : ℝ) : ℂ)) (fun i x => ?_) (expFun_mem N e)
  · convert h using 2 with i
    push_cast
    ring
  · rw [absChar, Units.val_mk0, abs_of_pos (Real.exp_pos x),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]

theorem expFun_mul (N : ℕ) (e : ℕ → ℝ) (g : Langlands.GeneralLinear N ℝ) {k : Langlands.GeneralLinear N ℝ}
    (hk : k ∈ unitaryCompact ℝ N) : expFun N e (g * k) = expFun N e g := by
  have h := rightTranslation_extension (χ := absChar e) (fun l => (e l : ℂ)) (absChar_eq e)
    (φ := fun _ => (1 : ℂ)) continuous_const ?_
    (fun a κ => by rw [principalSeriesCharacter_absChar_sign, one_mul]) ⟨_, hk⟩
  · have hk' : (Unitary.toUnits (⟨(k : Matrix (Fin N) (Fin N) ℝ), hk⟩ :
        Matrix.unitaryGroup (Fin N) ℝ) : Langlands.GeneralLinear N ℝ) = k := Units.ext rfl
    have := congrFun h g
    rw [hk'] at this
    exact this
  · have : (Set.range fun k : Matrix.unitaryGroup (Fin N) ℝ =>
        fun x : Matrix.unitaryGroup (Fin N) ℝ => (fun _ => (1 : ℂ)) (x * k)) =
        {fun _ => (1 : ℂ)} := Set.range_const
    rw [this]
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _)

theorem expFun_one (N : ℕ) (e : ℕ → ℝ) : expFun N e 1 = 1 := by
  have := extension_unitary (shiftedExponent N fun l => (e l : ℂ)) (fun _ => (1 : ℂ)) 1
  rw [map_one] at this
  exact this

/-! ## Modes -/

theorem not_isMode {M : ℕ} {j : ℤ} (h : ¬ IsMode M j) :
    |j| < M ∨ (-1 : ℂ) ^ j ≠ (-1) ^ (M + 1) := by
  by_contra hc
  rw [not_or, not_lt, not_not] at hc
  obtain ⟨h1, h2⟩ := hc
  apply h
  have hpar : (j + (M + 1 : ℕ)) % 2 = 0 := by
    rcases Int.even_or_odd j with hj | hj <;> rcases Nat.even_or_odd (M + 1) with hm | hm
    · rcases hj with ⟨r, rfl⟩
      rcases hm with ⟨q, hq⟩
      rw [hq]
      push_cast
      omega
    · rw [hj.neg_one_zpow, hm.neg_one_pow] at h2
      norm_num at h2
    · rw [hj.neg_one_zpow, hm.neg_one_pow] at h2
      norm_num at h2
    · rcases hj with ⟨r, rfl⟩
      rcases hm with ⟨q, hq⟩
      rw [hq]
      push_cast
      omega
  rcases abs_cases j with ⟨hj, hj0⟩ | ⟨hj, hj0⟩
  · refine ⟨(j.toNat - M - 1) / 2, Or.inl ?_⟩
    rw [hj] at h1
    push_cast
    omega
  · refine ⟨((-j).toNat - M - 1) / 2, Or.inr ?_⟩
    rw [hj] at h1
    push_cast
    omega

/-! ## The bound -/

/-- The exponent `e_i + (N - 1)/2 - i` of exponential equivariance. -/
def shiftExp (N : ℕ) (e : ℕ → ℂ) (i : Fin N) : ℂ := e i + ((N : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)

/-- The real exponent `t_i + (N - 1)/2 - i`. -/
def shiftExpRe (N : ℕ) (t : ℕ → ℝ) (i : Fin N) : ℝ := t i + ((N : ℝ) - 1) / 2 - ((i : ℕ) : ℝ)

theorem isExpEquivariant_of_mem {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (hχ : IsSignedPower χ e)
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : f ∈ principalSeries ℝ N χ) :
    RealBlockDerivative.IsExpEquivariant (shiftExp N e) f :=
  RealBlockDerivative.isExpEquivariant_of_mem_principalSeries (τ := fun i => e i)
    (fun i x => apply_exp hχ i x) hf

theorem inClass_slots {ds : List RealBlock} {h : Langlands.GeneralLinear N ℝ → ℂ}
    (hh : h ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N)) {D : ℕ}
    (hD : HasDegree (slots ds N) D h) : InClass (slots ds N) D h := by
  have hps : h ∈ principalSeries ℝ N (realPositionCharacter ds) := hh.1.1
  refine ⟨hps.1.continuous, hh.2, fun s hs => ?_⟩
  obtain ⟨p, hp, d, hd, rfl⟩ := mem_slots hs
  obtain ⟨hc1, hc2, he1, he2, -, -, -⟩ := induced_at hd
  refine ⟨?_, ?_, hD _ hs⟩
  · have hα := isExpEquivariant_of_mem (isSignedPower ds) hps
    have := isBlockCovariant_of_isExpEquivariant hp hα
    have e1 : shiftExp N (realPositionExponent ds) (ia hp) =
        realPositionExponent ds p + ((N : ℂ) - 1) / 2 - (p : ℂ) := rfl
    have e2 : shiftExp N (realPositionExponent ds) (ib hp) =
        realPositionExponent ds p + ((N : ℂ) - 1) / 2 - (p : ℂ) -
          ((d.weight.natAbs : ℂ) + 1) := by
      show realPositionExponent ds (p + 1) + ((N : ℂ) - 1) / 2 - ((p + 1 : ℕ) : ℂ) = _
      rw [he1, he2]
      push_cast
      ring
    rw [e1, e2] at this
    exact this
  · intro j hj g
    rcases not_isMode hj with h1 | h1
    · refine hh.1.2 p d hd j ?_ g
      rw [Int.abs_eq_natAbs d.weight]
      exact h1
    · refine blockFourierCoefficient_eq_zero_of_parity hp (realPositionCharacter_one ds) hps ?_ g
      rw [hc1, hc2]
      have a1 : realInducedFirstCharacter d (-1) = (-1) ^ (d.weight.natAbs + 1) := by
        simp [realInducedFirstCharacter]
      have a2 : realInducedSecondCharacter d (-1) = 1 := by
        simp [realInducedSecondCharacter]
      rw [a1, a2, mul_one]
      exact h1

/-- **The torus-pairing bound for real standard modules.** -/
theorem exists_bound {ds : List RealBlock} (hN : realRank ds = N)
    {u h : Langlands.GeneralLinear N ℝ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
      (unitaryCompact ℝ N))
    (hh : h ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N)) :
    ∃ C : ℝ, ∀ y1 y2 : Langlands.GeneralLinear N ℝ,
      ‖coeffs (zeroModes (slots ds N)) (fun x => u (x * y1) * h (x * y2)) 1‖ ≤
        C * ‖coeffs (zeroModes (slots ds N)) (fun x =>
          expFun N (fun l => -realPositionBlockExponent ds l) (x * y1) *
            expFun N (realPositionBlockExponent ds) (x * y2)) 1‖ := by
  have hpsu : u ∈ principalSeries ℝ N (dualChar (realPositionCharacter ds)) := hu.1
  have hps : h ∈ principalSeries ℝ N (realPositionCharacter ds) := hh.1.1
  obtain ⟨Du, hDu⟩ := exists_hasDegree hpsu.1.continuous hu.2 (slots ds N)
  obtain ⟨Dh, hDh⟩ := exists_hasDegree hps.1.continuous hh.2 (slots ds N)
  have hαu := isExpEquivariant_of_mem (isSignedPower ds).dual hpsu
  have hαh := isExpEquivariant_of_mem (isSignedPower ds) hps
  have hblock : ∀ s ∈ slots ds N, ∃ d : ComplexCharacterData,
      realInducedBlockAt ds s.p = some d ∧ s.M = d.weight.natAbs ∧
        s.α = realPositionExponent ds s.p + ((N : ℂ) - 1) / 2 - (s.p : ℂ) := by
    intro s hs
    obtain ⟨p, hp, d, hd, rfl⟩ := mem_slots hs
    exact ⟨d, hd, rfl, rfl⟩
  refine norm_coeffs_le_mul_norm_coeffs (max Du Dh) (pairwise_slots ds N)
    (σu := shiftExpRe N fun l => -realPositionBlockExponent ds l)
    (σh := shiftExpRe N (realPositionBlockExponent ds))
    hpsu.1 hαu hu.2 (hasDegree_mono (le_max_left _ _) hDu) hps.1 hαh
    (inClass_slots hh (hasDegree_mono (le_max_right _ _) hDh))
    (contMDiff_expFun N _) (isExpEquivariant_expFun N _) (fun g k hk => expFun_mul N _ g hk)
    (expFun_one N _)
    (contMDiff_expFun N _) (isExpEquivariant_expFun N _) (fun g k hk => expFun_mul N _ g hk)
    (expFun_one N _) ?_ ?_ ?_ ?_ ?_ ?_
  · intro s _
    simp only [shiftExp, ia, ib]
    push_cast
    ring
  · intro s _
    simp only [shiftExpRe, ia, ib]
    push_cast
    ring
  · intro s _
    simp only [shiftExp, shiftExpRe, ia]
    simp
    ring
  · intro s hs
    obtain ⟨d, hd, -, -⟩ := hblock s hs
    obtain ⟨-, -, -, -, hb1, hb2, -⟩ := induced_at hd
    simp only [shiftExpRe, ia, ib]
    rw [hb1, hb2]
    push_cast
    ring
  · intro s hs
    obtain ⟨d, hd, hM, hα⟩ := hblock s hs
    obtain ⟨-, -, he1, -, hb1, -, -⟩ := induced_at hd
    simp only [shiftExpRe, ia]
    rw [hb1, hα, he1, hM]
    simp
    ring
  · intro i hi
    have hre := exponent_re_eq ds i fun p d hd => by
      have hp : p + 1 < N := hN ▸ realInducedBlockAt_lt hd
      have := hi _ (mkSlot_mem_slots hd hp)
      simp only [ia, ib, mkSlot, ne_eq, Fin.ext_iff] at this
      exact this
    refine ⟨?_, ?_⟩
    · simp only [shiftExp, shiftExpRe]
      simp [hre]
    · simp only [shiftExp, shiftExpRe]
      simp [hre]

end RealInducedStandardBound

open RealInducedBlockBound RealInducedTorusCore RealInducedStandardBound PartialJacquet in
/-- **The torus-pairing bound for real standard modules.** Let `ds` be a list of real blocks of
total rank `N`, `h` an `O(N)`-finite function of `realStandardModule N ds` and `u` an
`O(N)`-finite function of the dual principal series of the position characters. Let
`slots ds N` be the induction blocks of `ds` and `t_l` the real part of the exponent of the block
containing the position `l`. Then there is `C` such that for all `y_1, y_2`
`|∫_T u(τ y_1) h(τ y_2) dτ| ≤ C |∫_T E_u(τ y_1) E_h(τ y_2) dτ|`, where `T` is the torus of
rotations of the induction blocks (the iterated mode-`0` Fourier coefficient) and
`E_h = expFun N t`, `E_u = expFun N (−t)`. -/
def RealInducedStandardBoundStatement : Prop :=
  ∀ (N : ℕ) (ds : List RealBlock), realRank ds = N →
    ∀ u ∈ kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
        (unitaryCompact ℝ N),
    ∀ h ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N),
    ∃ C : ℝ, ∀ y1 y2 : Langlands.GeneralLinear N ℝ,
      ‖coeffs (zeroModes (slots ds N)) (fun x => u (x * y1) * h (x * y2)) 1‖ ≤
        C * ‖coeffs (zeroModes (slots ds N)) (fun x =>
          expFun N (fun l => -realPositionBlockExponent ds l) (x * y1) *
            expFun N (realPositionBlockExponent ds) (x * y2)) 1‖

theorem realInducedStandardBound : RealInducedStandardBoundStatement :=
  fun _ _ hN _ hu _ hh => RealInducedStandardBound.exists_bound hN hu hh

end Langlands.Archimedean
