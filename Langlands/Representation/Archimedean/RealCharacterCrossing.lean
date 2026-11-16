import Langlands.Representation.Archimedean.RealLanglandsQuotientReduction
import Langlands.Representation.Archimedean.RealLinkedJacquetFunctionalCases
import Langlands.Representation.Archimedean.RealBlockJacquetFunctional
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.Archimedean.JacquetNonvanishing
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The linked Jacquet functional for lists of real characters

This file proves `RealCharacterLinkedJacquetFunctionalStatement`
(`realCharacterLinkedJacquetFunctional`): S2 for Langlands-ordered lists of real characters with
a linked pair of Mœglin data.

A list of characters is written `PL τ e`, the characters `sgn^{e_i} |·|^{τ_i}`, `i < n`.
`Concl n ds` is the conclusion of the statement for the list `ds`; it passes back along
surjective `(𝔤, K)`-intertwiners (`concl_of_surjective`).

* **Crossings.** For `r + 1 < n` and a multiplier `μ` solving the recurrence of the block
  `r, r + 1`, the block Fourier multiplier functional `blockJacquet n (PL τ e) r μ` is a real
  Jacquet functional with the exponents of the list with `r, r + 1` exchanged
  (`isJacquet_cross`); its Frobenius map `frobMap` is an intertwiner into the principal series of
  the exchanged list.
* **Generic crossings.** If `ν = τ_r - τ_{r+1}` has `0 ≤ re ν` and the two characters are not
  linked, the generic multiplier has no zeros, the crossing with the inverse multiplier is a
  right inverse, and the conclusion for the exchanged list gives the conclusion for `PL τ e`
  (`concl_of_generic`).
* **The linked adjacent pair.** If `τ_r - τ_{r+1} = k > 0` and `k + e_r + e_{r+1}` is odd, the
  binomial multiplier gives a nonzero functional (`blockJacquet_PL_ne_zero`, by a test vector)
  that kills `π(E_{r+1,r})^k` (`blockJacquet_pow_eq_zero`: along `e(s) = 1 + s E_{r+1,r}` the
  Frobenius function is a polynomial of degree `< k`, by the Iwasawa decomposition of `e(s)`).
  This is `concl_of_linked_adjacent`.
* **Assembly.** A linked pair `i < j` is moved to an adjacent pair by generic crossings at
  `j - 1`, by induction on `j - i - 1` (`concl_of_lk`, `concl_of_char`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealCharacterCrossing

open Langlands.LocalFactor.Archimedean
open RealJacquetFrobenius RealBlockJacquet RealBlockMultiplier RealBlockRotation
  RealBlockFourierFinite RealLinkedJacquetFunctional

variable {n : ℕ}

/-- The `O(n)`-finite functions of the standard module of `ds`. -/
abbrev KF (n : ℕ) (ds : List RealBlock) :=
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

/-! ## Lists of characters by position exponents -/

/-- The list of the real characters `sgn^{e_i} |·|^{τ_i}`. -/
def PL (τ : Fin n → ℂ) (e : Fin n → Fin 2) : List RealBlock :=
  (List.ofFn fun i => charData (e i) (τ i)).map RealBlock.character

theorem chars_list_eq (a : Fin n → ℂ) (e : Fin n → Fin 2) :
    (List.ofFn (chars a e)).map RealBlock.character = PL (expo a) e :=
  rfl

theorem PL_position (τ : Fin n → ℂ) (e : Fin n → Fin 2) (i : Fin n) (x : ℝˣ) :
    realPositionCharacter (PL τ e) i x = charFun (e i) (τ i) x := by
  rw [PL, realPositionCharacter_map_character _ i (by simp)]
  simp [List.getElem_ofFn, charData_character_apply]

theorem PL_position_neg_one (τ : Fin n → ℂ) (e : Fin n → Fin 2) (i : Fin n) :
    realPositionCharacter (PL τ e) i (-1) = (-1) ^ (e i).val := by
  rw [PL_position]
  have : ((-1 : ℝˣ) : ℝ) = -1 := by simp
  rw [this, charFun_neg_one]

theorem PL_position_exp (τ : Fin n → ℂ) (e : Fin n → Fin 2) (i : Fin n) (x : ℝ) :
    realPositionCharacter (PL τ e) i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
      Complex.exp (τ i * x) := by
  rw [PL_position, charFun_of_pos _ _ (by simpa using Real.exp_pos x)]
  rw [show ((Units.mk0 (Real.exp x) (Real.exp_pos x).ne' : ℝˣ) : ℝ) = Real.exp x from rfl,
    Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp]
  · ring_nf
  · simp [Complex.ofReal_im, Real.pi_pos]
  · simp [Complex.ofReal_im, Real.pi_pos.le]

/-! ## The conclusion of the linked Jacquet functional statement -/

/-- The conclusion of `RealLinkedJacquetFunctionalStatement` for the list `ds`. -/
def Concl (n : ℕ) (ds : List RealBlock) : Prop :=
  ∃ (ℓ : (KF n ds) →ₗ[ℂ] ℂ) (a : Fin n → ℂ) (e : Fin n → Fin 2) (p k : ℕ) (hp : p + 1 < n),
    ℓ ≠ 0 ∧ IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e ∧
      a ⟨p, Nat.lt_of_succ_lt hp⟩ - a ⟨p + 1, hp⟩ = 1 - (k : ℂ) ∧
      ∀ v : KF n ds, ℓ ((realStandardLie n ds (1 ⊗ₜ lowerRootMatrix n p hp) ^ k) v) = 0

/-- **Transport.** The conclusion passes back along a surjective intertwiner. -/
theorem concl_of_surjective {ds ds' : List RealBlock} (B : (KF n ds) →ₗ[ℂ] (KF n ds'))
    (hB : Function.Surjective B)
    (hrep : ∀ κ v, B (realStandardRep n ds κ v) = realStandardRep n ds' κ (B v))
    (hlie : ∀ Y v, B (realStandardLie n ds Y v) = realStandardLie n ds' Y (B v))
    (h : Concl n ds') : Concl n ds := by
  obtain ⟨ℓ, a, e, p, k, hp, h0, hJ, ha, hY⟩ := h
  refine ⟨ℓ ∘ₗ B, a, e, p, k, hp, ?_, ⟨fun X hX v => ?_, fun j v => ⟨?_, ?_⟩⟩, ha, fun v => ?_⟩
  · intro hz
    apply h0
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := hB w
    exact LinearMap.congr_fun hz v
  · simp only [LinearMap.comp_apply, hlie]
    exact hJ.1 X hX (B v)
  · simp only [LinearMap.comp_apply, hlie]
    exact (hJ.2 j (B v)).1
  · simp only [LinearMap.comp_apply, hrep]
    exact (hJ.2 j (B v)).2
  · have hpow : ∀ (m : ℕ) (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (w : KF n ds),
        B ((realStandardLie n ds Y ^ m) w) = (realStandardLie n ds' Y ^ m) (B w) := by
      intro m Y
      induction m with
      | zero => intro w; simp
      | succ m ih =>
        intro w
        rw [pow_succ, Module.End.mul_apply, ih, hlie, pow_succ, Module.End.mul_apply]
    simp only [LinearMap.comp_apply, hpow]
    exact hY (B v)

/-! ## The Frobenius map of a Jacquet functional -/

section Frob

variable {ds : List RealBlock} {ℓ : (KF n ds) →ₗ[ℂ] ℂ} {a : Fin n → ℂ} {e : Fin n → Fin 2}

theorem frob_mem (hℓ : IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e)
    (v : KF n ds) :
    frobLin (realStandardRep n ds) ℓ a e v ∈ KF n (PL (expo a) e) := by
  have hgk := isRealGKModule_realStandardModule n ds
  have hsign : ∀ (j : Fin n) (v : KF n ds),
      ℓ (realStandardRep n ds (signReflection n j) v) = (-1) ^ (e j).val * ℓ v :=
    fun j v => (hℓ.2 j v).2
  refine Submodule.mem_inf.mpr ⟨⟨(mem_principalSeries_iff ℝ n _ _).mpr
    ⟨contMDiff_frobFun hsign hgk.1 hgk.2.1 v, frobFun_left hsign v⟩, ?_⟩,
    frobFun_mem_kFiniteVectors hsign v (hgk.1 v)⟩
  intro q d hd
  rw [← chars_list_eq, RealPrincipalSeriesDuality.realInducedBlockAt_map_character] at hd
  exact absurd hd (by simp)

/-- The Frobenius map `v ↦ (g ↦ ℓ(...))` of a real Jacquet functional, into the principal series
of the characters `sgn^{e_i} |·|^{expo a i}`. -/
def frobMap (hℓ : IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e) :
    (KF n ds) →ₗ[ℂ] (KF n (PL (expo a) e)) :=
  (frobLin (realStandardRep n ds) ℓ a e).codRestrict _ (frob_mem hℓ)

theorem frobMap_coe
    (hℓ : IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e)
    (v : KF n ds) :
    ((frobMap hℓ v : KF n (PL (expo a) e)) : Langlands.GeneralLinear n ℝ → ℂ) =
      frobFun (realStandardRep n ds) ℓ a e v :=
  rfl

theorem frobMap_rep
    (hℓ : IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) (v : KF n ds) :
    frobMap hℓ (realStandardRep n ds κ v) =
      realStandardRep n (PL (expo a) e) κ (frobMap hℓ v) :=
  frobLin_codRestrict_rep (fun j v => (hℓ.2 j v).2) (frob_mem hℓ) κ v

theorem frobMap_lie
    (hℓ : IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e)
    (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (v : KF n ds) :
    frobMap hℓ (realStandardLie n ds Y v) =
      realStandardLie n (PL (expo a) e) Y (frobMap hℓ v) :=
  frobLin_codRestrict_lie (isRealGKModule_realStandardModule n ds) hℓ (frob_mem hℓ) Y v

theorem frobMap_apply_one
    (hℓ : IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e)
    (v : KF n ds) :
    (frobMap hℓ v : Langlands.GeneralLinear n ℝ → ℂ) 1 = ℓ v :=
  frobFun_apply_one (fun j v => (hℓ.2 j v).2) v

end Frob

/-! ## Crossings of adjacent positions -/

section Crossing

variable {r : ℕ} (hr : r + 1 < n)

/-- The transposition of the positions `r` and `r + 1`. -/
def sw : Equiv.Perm (Fin n) := Equiv.swap (ia hr) (ib hr)

theorem sw_ia : sw hr (ia hr) = ib hr := Equiv.swap_apply_left _ _

theorem sw_ib : sw hr (ib hr) = ia hr := Equiv.swap_apply_right _ _

theorem sw_of_ne {i : Fin n} (h1 : i ≠ ia hr) (h2 : i ≠ ib hr) : sw hr i = i :=
  Equiv.swap_apply_of_ne_of_ne h1 h2

theorem sw_sw (i : Fin n) : sw hr (sw hr i) = i := Equiv.swap_apply_self _ _ _

/-- The Frobenius exponents of the crossing at `r`: the `ρ`-shifted exponents of the list with
the positions `r, r + 1` exchanged. -/
def crossExp (τ : Fin n → ℂ) (i : Fin n) : ℂ :=
  τ (sw hr i) + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)

theorem expo_crossExp (τ : Fin n → ℂ) : expo (crossExp hr τ) = τ ∘ sw hr := by
  funext i
  simp only [expo, crossExp, Function.comp_apply]
  ring

theorem crossExp_sub (τ : Fin n → ℂ) :
    crossExp hr τ (ia hr) - crossExp hr τ (ib hr) = τ (ib hr) - τ (ia hr) + 1 := by
  simp only [crossExp, sw_ia, sw_ib]
  simp only [ia, ib]
  push_cast
  ring

/-- The parity class `e_r + e_{r+1} mod 2` of the block Fourier modes at `r, r + 1`. -/
def par (e : Fin n → Fin 2) : ℕ := ((e (ia hr)).val + (e (ib hr)).val) % 2

theorem par_cases (e : Fin n → Fin 2) :
    ((par hr e : ℕ) : ℤ) = 0 ∨ ((par hr e : ℕ) : ℤ) = 1 := by
  unfold par
  omega

theorem neg_one_pow_par (e : Fin n → Fin 2) :
    (-1 : ℂ) ^ par hr e = (-1) ^ (e (ia hr)).val * (-1) ^ (e (ib hr)).val := by
  rw [par, ← neg_one_pow_eq_pow_mod_two, pow_add]

theorem par_comp_sw (e : Fin n → Fin 2) : par hr (e ∘ sw hr) = par hr e := by
  simp only [par, Function.comp_apply, sw_ia, sw_ib, Nat.add_comm]

theorem neg_one_pow_mul_self (m : ℕ) : (-1 : ℂ) ^ m * (-1) ^ m = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem inv_neg_one_pow (m : ℕ) : ((-1 : ℂ) ^ m)⁻¹ = (-1) ^ m := by
  rw [← inv_pow, inv_neg_one]

theorem PL_parity (τ : Fin n → ℂ) (e : Fin n → Fin 2) :
    (-1 : ℂ) ^ ((par hr e : ℕ) : ℤ) =
      realPositionCharacter (PL τ e) r (-1) * realPositionCharacter (PL τ e) (r + 1) (-1) := by
  have h1 : realPositionCharacter (PL τ e) r (-1) = (-1) ^ (e (ia hr)).val :=
    PL_position_neg_one τ e (ia hr)
  have h2 : realPositionCharacter (PL τ e) (r + 1) (-1) = (-1) ^ (e (ib hr)).val :=
    PL_position_neg_one τ e (ib hr)
  rw [zpow_natCast, neg_one_pow_par, h1, h2]

/-- **Crossing.** A symmetric solution of the recurrence for `δ = τ_r - τ_{r+1} + 1` on the
parity class of the block gives a real Jacquet functional on the principal series of
`PL τ e`, with the Frobenius exponents of `τ ∘ sw` and the signs `e ∘ sw`. -/
theorem isJacquet_cross (τ : Fin n → ℂ) (e : Fin n → Fin 2) {μ : ℤ → ℂ}
    (hrec : IsRecurrent (τ (ia hr) - τ (ib hr) + 1) (par hr e) μ)
    (hsym : IsSymmetric (par hr e) ((-1) ^ par hr e) μ) :
    IsRealJacquetFunctional n (realStandardRep n (PL τ e)) (realStandardLie n (PL τ e))
      (blockJacquet n (PL τ e) r μ) (crossExp hr τ) (e ∘ sw hr) := by
  have hpos : ∀ i : Fin n, realPositionCharacter (PL τ e) i (-1) = (-1) ^ (e i).val :=
    PL_position_neg_one τ e
  have h1 : realPositionCharacter (PL τ e) r (-1) = (-1) ^ (e (ia hr)).val := hpos (ia hr)
  have h2 : realPositionCharacter (PL τ e) (r + 1) (-1) = (-1) ^ (e (ib hr)).val := hpos (ib hr)
  have hδ : (τ (ia hr) + ((n : ℂ) - 1) / 2 - (((ia hr : Fin n) : ℕ) : ℂ)) -
      (τ (ib hr) + ((n : ℂ) - 1) / 2 - (((ib hr : Fin n) : ℕ) : ℂ)) =
      τ (ia hr) - τ (ib hr) + 1 := by
    simp only [ia, ib]
    push_cast
    ring
  have hsq := neg_one_pow_mul_self (e (ia hr)).val
  have hsq' := neg_one_pow_mul_self (e (ib hr)).val
  refine isRealJacquetFunctional_blockJacquet hr (PL_position_exp τ e) (PL_parity hr τ e)
    (by rw [hδ]; exact hrec) (σ := (-1) ^ par hr e) hsym (fun i hi1 hi2 => ?_) ?_ ?_
    (fun i hi1 hi2 => ?_) ?_ ?_
  · simp only [crossExp, sw_of_ne hr hi1 hi2]
  · simp only [crossExp, sw_ia]
    simp only [ia, ib]
    push_cast
    ring
  · simp only [crossExp, sw_ib]
    simp only [ia, ib]
    push_cast
    ring
  · rw [Function.comp_apply, sw_of_ne hr hi1 hi2, hpos]
  · rw [Function.comp_apply, sw_ia, h1, neg_one_pow_par]
    linear_combination (-(-1 : ℂ) ^ (e (ib hr)).val) * hsq
  · rw [Function.comp_apply, sw_ib, h2, neg_one_pow_par]
    linear_combination (-(-1 : ℂ) ^ (e (ia hr)).val) * hsq'

end Crossing

/-! ## The generic multiplier for `0 ≤ re ν` -/

section Generic

open Finset

theorem generic_denom_ne_zero {ν : ℂ} (hν : 0 ≤ ν.re) {ε : ℤ} (hε : 0 ≤ ε) (i : ℕ) :
    (ε : ℂ) + 2 * i + 1 + ν ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, Complex.one_re, Complex.re_ofNat, Complex.im_ofNat, Complex.zero_re,
    mul_zero, sub_zero] at h'
  have hε' : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

theorem genericSeq_succ' {ν : ℂ} (hν : 0 ≤ ν.re) {ε : ℤ} (hε : 0 ≤ ε) (m : ℕ) :
    genericSeq ν ε (m + 1) * (ν + 1 + ε + 2 * m) =
      ((ε : ℂ) + 2 * m + 2 - (ν + 1)) * genericSeq ν ε m := by
  have hd := generic_denom_ne_zero hν hε m
  rw [genericSeq, prod_range_succ, ← genericSeq]
  field_simp
  ring

theorem isRecurrent_generic {ν : ℂ} (hν : 0 ≤ ν.re) {ε : ℤ} (hε : ε = 0 ∨ ε = 1) :
    IsRecurrent (ν + 1) ε (genericMultiplier ν ε) :=
  isRecurrent_extend hε (neg_one_pow_sq _) (Or.inr rfl) fun m => by
    have h0 : 0 ≤ ε := by omega
    have := genericSeq_succ' hν h0 m
    linear_combination this

theorem generic_ne_zero {ν : ℂ} (hν : 0 ≤ ν.re) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hne : ∀ m : ℕ, ν ≠ (ε : ℂ) + 2 * m + 1) (k : ℤ) : genericMultiplier ν ε k ≠ 0 := by
  refine (extend_ne_zero_iff (pow_ne_zero _ (by norm_num)) k).mpr ?_
  rw [genericSeq, prod_ne_zero_iff]
  intro i _
  exact div_ne_zero (sub_ne_zero.mpr (hne i).symm) (generic_denom_ne_zero hν (by omega) i)

end Generic

/-! ## Generic crossings are surjective -/

section GenericCrossing

variable {r : ℕ} (hr : r + 1 < n)

theorem PL_sw_sw (τ : Fin n → ℂ) (e : Fin n → Fin 2) :
    PL (expo (crossExp hr (expo (crossExp hr τ)))) ((e ∘ sw hr) ∘ sw hr) = PL τ e := by
  have h1 : expo (crossExp hr (expo (crossExp hr τ))) = τ := by
    rw [expo_crossExp, expo_crossExp]
    funext i
    simp [sw_sw]
  have h2 : (e ∘ sw hr) ∘ sw hr = e := by
    funext i
    simp [sw_sw]
  rw [h1, h2]

/-- **Generic crossing.** If `ν = τ_r - τ_{r+1}` has `0 ≤ re ν` and the characters at `r, r + 1`
are not linked (`ν ≠ ε + 2m + 1`), the conclusion for the list with `r, r + 1` exchanged gives
the conclusion for `PL τ e`. -/
theorem concl_of_generic (τ : Fin n → ℂ) (e : Fin n → Fin 2)
    (hν : 0 ≤ (τ (ia hr) - τ (ib hr)).re)
    (hne : ∀ m : ℕ, τ (ia hr) - τ (ib hr) ≠ ((par hr e : ℕ) : ℂ) + 2 * m + 1)
    (h : Concl n (PL (τ ∘ sw hr) (e ∘ sw hr))) : Concl n (PL τ e) := by
  set ν := τ (ia hr) - τ (ib hr) with hνdef
  set ε : ℤ := ((par hr e : ℕ) : ℤ) with hεdef
  have hε : ε = 0 ∨ ε = 1 := par_cases hr e
  set μ := genericMultiplier ν ε with hμ
  have hne' : ∀ m : ℕ, ν ≠ (ε : ℂ) + 2 * m + 1 := fun m => by
    rw [hεdef]
    push_cast
    exact hne m
  have hμ0 : ∀ k, μ k ≠ 0 := generic_ne_zero hν hε hne'
  have hrec : IsRecurrent (ν + 1) ε μ := isRecurrent_generic hν hε
  have hsym : IsSymmetric ε ((-1) ^ par hr e) μ := isSymmetric_genericMultiplier ν hε
  have hJ := isJacquet_cross hr τ e hrec hsym
  rw [← expo_crossExp] at h
  refine concl_of_surjective (frobMap hJ) ?_ (frobMap_rep hJ) (frobMap_lie hJ) h
  -- the inverse crossing
  set τ' := expo (crossExp hr τ) with hτ'
  set e' := e ∘ sw hr with he'
  have hpar' : par hr e' = par hr e := par_comp_sw hr e
  have hδ' : τ' (ia hr) - τ' (ib hr) + 1 = 2 - (ν + 1) := by
    rw [hτ', expo_crossExp]
    simp only [Function.comp_apply, sw_ia, sw_ib, hνdef]
    ring
  have hrec' : IsRecurrent (τ' (ia hr) - τ' (ib hr) + 1) (par hr e') fun k => (μ k)⁻¹ := by
    rw [hδ', hpar']
    exact hrec.inv fun k _ => hμ0 k
  have hsym' : IsSymmetric (par hr e') ((-1) ^ par hr e') fun k => (μ k)⁻¹ := by
    have := hsym.inv
    rw [inv_neg_one_pow] at this
    rw [hpar']
    exact this
  have hJ' := isJacquet_cross hr τ' e' hrec' hsym'
  have hlist := PL_sw_sw hr τ e
  intro g
  refine ⟨⟨(frobMap hJ' g : Langlands.GeneralLinear n ℝ → ℂ), hlist ▸ (frobMap hJ' g).2⟩, ?_⟩
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries (frobMap hJ _).2.1.1 g.2.1.1
    fun κ hκ => ?_
  rw [eq_finsum_blockFourierCoefficient hr (continuous_coe _) (frobMap hJ _).2.2 hκ,
    eq_finsum_blockFourierCoefficient hr (continuous_coe g) g.2.2 hκ]
  congr 2
  funext j
  have hsignJ : ∀ (i : Fin n) (v : KF n (PL τ e)),
      blockJacquet n (PL τ e) r μ (realStandardRep n (PL τ e) (signReflection n i) v) =
        (-1) ^ ((e ∘ sw hr) i).val * blockJacquet n (PL τ e) r μ v := fun i v => (hJ.2 i v).2
  have hsignJ' : ∀ (i : Fin n) (v : KF n (PL τ' e')),
      blockJacquet n (PL τ' e') r (fun k => (μ k)⁻¹)
          (realStandardRep n (PL τ' e') (signReflection n i) v) =
        (-1) ^ ((e' ∘ sw hr) i).val * blockJacquet n (PL τ' e') r (fun k => (μ k)⁻¹) v :=
    fun i v => (hJ'.2 i v).2
  rw [frobMap_coe, blockFourierCoefficient_frobFun hr hsignJ _ hκ j]
  change μ j * blockFourierCoefficient n r j
    (RealJacquetFrobenius.frobFun (realStandardRep n (PL τ' e'))
      (blockJacquet n (PL τ' e') r fun k => (μ k)⁻¹) (crossExp hr τ') (e' ∘ sw hr) g) κ = _
  rw [blockFourierCoefficient_frobFun hr hsignJ' _ hκ j, ← mul_assoc,
    mul_inv_cancel₀ (hμ0 j), one_mul]

end GenericCrossing

/-! ## Polynomials along the real line -/

section Poly

open Polynomial

theorem iteratedDeriv_eval (q : ℂ[X]) (m : ℕ) :
    iteratedDeriv m (fun t : ℝ => q.eval (t : ℂ)) =
      fun t : ℝ => (derivative^[m] q).eval (t : ℂ) := by
  induction m generalizing q with
  | zero => rfl
  | succ m ih =>
    have hd : deriv (fun t : ℝ => q.eval (t : ℂ)) = fun t : ℝ => (derivative q).eval (t : ℂ) :=
      funext fun t => ((q.hasDerivAt (t : ℂ)).comp_ofReal).deriv
    rw [iteratedDeriv_succ', hd, ih, Function.iterate_succ_apply]

theorem iteratedDeriv_eval_eq_zero {q : ℂ[X]} {m : ℕ} (hq : q.natDegree < m) (t : ℝ) :
    iteratedDeriv m (fun t : ℝ => q.eval (t : ℂ)) t = 0 := by
  rw [iteratedDeriv_eval, iterate_derivative_eq_zero hq]
  simp

end Poly

/-! ## The angle `arctan t` -/

section Trig

theorem sqrt_one_add_sq_pos (t : ℝ) : 0 < Real.sqrt (1 + t ^ 2) :=
  Real.sqrt_pos.mpr (by positivity)

theorem I_mul_add_one (t : ℝ) :
    Complex.I * t + 1 =
      (Real.sqrt (1 + t ^ 2) : ℂ) * Complex.exp (Real.arctan t * Complex.I) := by
  have hS : (Real.sqrt (1 + t ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sqrt_one_add_sq_pos t).ne'
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_arctan,
    Real.sin_arctan]
  push_cast
  field_simp
  ring

theorem neg_I_mul_add_one (t : ℝ) :
    -Complex.I * t + 1 =
      (Real.sqrt (1 + t ^ 2) : ℂ) * Complex.exp (-(Real.arctan t * Complex.I)) := by
  have hS : (Real.sqrt (1 + t ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sqrt_one_add_sq_pos t).ne'
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_arctan, Real.sin_arctan]
  push_cast
  field_simp
  ring

/-- `(1 + it)^a (1 - it)^b = S^{a+b} e^{i(a-b)θ}` for `θ = arctan t`, `S = √(1 + t²)`. -/
theorem pow_mul_pow_eq (t : ℝ) (a b : ℕ) (j : ℤ) (hj : j = (a : ℤ) - b) :
    (Complex.I * t + 1) ^ a * (-Complex.I * t + 1) ^ b =
      (Real.sqrt (1 + t ^ 2) : ℂ) ^ (a + b) *
        Complex.exp ((j : ℂ) * (Real.arctan t : ℂ) * Complex.I) := by
  rw [I_mul_add_one, neg_I_mul_add_one, mul_pow, mul_pow, ← Complex.exp_nat_mul,
    ← Complex.exp_nat_mul, pow_add]
  have h : Complex.exp ((j : ℂ) * (Real.arctan t : ℂ) * Complex.I) =
      Complex.exp (a * (Real.arctan t * Complex.I)) *
        Complex.exp (b * -(Real.arctan t * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hj]
    push_cast
    ring
  rw [h]
  ring

theorem cos_eq_expMode (θ : ℝ) :
    (Real.cos θ : ℂ) = (expMode 1 θ + expMode (-1) θ) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos]
  simp only [expMode]
  push_cast
  ring_nf

theorem cos_two_mul_eq_expMode (θ : ℝ) :
    (Real.cos (2 * θ) : ℂ) = (expMode 2 θ + expMode (-2) θ) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos]
  simp only [expMode]
  push_cast
  ring_nf

/-- The Fourier coefficient of `cos^m` in the parity class of `m`, for `m ≤ 2`, is nonzero. -/
theorem coeff_cos_pow_ne_zero {m : ℕ} (hm : m ≤ 2) :
    coeff ((m % 2 : ℕ) : ℤ) (fun θ => (Real.cos θ : ℂ) ^ m) ≠ 0 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  interval_cases m
  · have h : (fun θ : ℝ => (Real.cos θ : ℂ) ^ 0) = expMode 0 :=
      funext fun θ => by rw [pow_zero, expMode_zero_left]
    rw [h, coeff_expMode]
    simp
  · have h : (fun θ : ℝ => (Real.cos θ : ℂ) ^ 1) =
        (1 / 2 : ℂ) • expMode 1 + (1 / 2 : ℂ) • expMode (-1) := by
      funext θ
      simp only [pow_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, cos_eq_expMode]
      ring
    rw [h, coeff_add ((continuous_expMode 1).const_smul _) ((continuous_expMode _).const_smul _),
      coeff_smul, coeff_smul, coeff_expMode, coeff_expMode]
    norm_num
  · have h : (fun θ : ℝ => (Real.cos θ : ℂ) ^ 2) =
        (1 / 2 : ℂ) • expMode 0 + ((1 / 4 : ℂ) • expMode 2 + (1 / 4 : ℂ) • expMode (-2)) := by
      funext θ
      have h2 := cos_two_mul_eq_expMode θ
      rw [Real.cos_two_mul] at h2
      push_cast at h2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, expMode_zero_left]
      rw [Complex.ofReal_cos]
      linear_combination (1 / 2 : ℂ) * h2
    rw [h, coeff_add ((continuous_expMode 0).const_smul _)
      (((continuous_expMode 2).const_smul _).add ((continuous_expMode _).const_smul _)),
      coeff_add ((continuous_expMode 2).const_smul _) ((continuous_expMode _).const_smul _),
      coeff_smul, coeff_smul, coeff_smul, coeff_expMode, coeff_expMode, coeff_expMode]
    norm_num

end Trig

/-! ## The Iwasawa decomposition of `e(s)` -/

section Iwasawa

variable {r : ℕ} (hr : r + 1 < n)

theorem lowerRootElement_zero' : lowerRootElement n r hr 0 = 1 := by
  apply Units.ext
  simp

/-- The upper triangular factor `b(s) = e(s) r_p(-arctan s)` of `e(s) = b(s) r_p(arctan s)`. -/
def iwaB (s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (lowerRootElement n r hr s : Matrix (Fin n) (Fin n) ℝ) *
    (blockRotation n r (-Real.arctan s) : Matrix (Fin n) (Fin n) ℝ)

theorem iwaB_mul (s : ℝ) :
    (lowerRootElement n r hr s : Matrix (Fin n) (Fin n) ℝ) =
      iwaB hr s * (blockRotation n r (Real.arctan s) : Matrix (Fin n) (Fin n) ℝ) := by
  rw [iwaB, mul_assoc, ← Units.val_mul, ← blockRotation_add, neg_add_cancel, blockRotation_zero,
    Units.val_one, mul_one]

theorem iwaB_apply (s : ℝ) (i j : Fin n) :
    iwaB hr s i j = (blockRotation n r (-Real.arctan s) : Matrix (Fin n) (Fin n) ℝ) i j +
      if (i : ℕ) = r + 1 then
        s * (blockRotation n r (-Real.arctan s) : Matrix (Fin n) (Fin n) ℝ) (ia hr) j
      else 0 := by
  rw [iwaB, lowerRootElement_val, add_mul, one_mul, Matrix.add_apply, smul_mul_assoc,
    Matrix.smul_apply, lowerRootMatrix]
  split_ifs with h
  · have hi : i = ⟨r + 1, hr⟩ := Fin.ext h
    subst hi
    rw [Matrix.single_mul_apply_same, one_mul, smul_eq_mul]
    rfl
  · have h0 : (Matrix.single (⟨r + 1, hr⟩ : Fin n) (⟨r, by omega⟩ : Fin n) (1 : ℝ) *
        (blockRotation n r (-Real.arctan s) : Matrix (Fin n) (Fin n) ℝ)) i j = 0 :=
      Matrix.single_mul_apply_of_ne _ _ _ _ _ (fun h' => h (by rw [h'])) _
    rw [h0, smul_zero]

theorem iwaB_upper (s : ℝ) : (iwaB hr s).IsUpperTriangular := by
  intro i j hji
  have hji' : (j : ℕ) < i := hji
  rw [iwaB_apply, blockRotation_apply hr, blockRotation_apply hr]
  simp only [ia, Real.sin_neg, Real.cos_neg, Fin.ext_iff, true_and, and_true, true_or]
  split_ifs <;> first | (exfalso; omega) | simp | skip
  have hS := sqrt_one_add_sq_pos s
  rw [Real.cos_arctan, Real.sin_arctan]
  field_simp
  ring

theorem iwaB_ia (s : ℝ) : iwaB hr s (ia hr) (ia hr) = 1 / Real.sqrt (1 + s ^ 2) := by
  rw [iwaB_apply, blockRotation_apply hr]
  simp only [ia, Real.cos_neg, true_and, and_true, true_or]
  split_ifs <;> first | (exfalso; omega) | skip
  rw [add_zero, Real.cos_arctan]

theorem iwaB_ib (s : ℝ) : iwaB hr s (ib hr) (ib hr) = Real.sqrt (1 + s ^ 2) := by
  have hS := sqrt_one_add_sq_pos s
  have hS2 : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  rw [iwaB_apply, blockRotation_apply hr, blockRotation_apply hr]
  simp only [ia, ib, Real.cos_neg, Real.sin_neg, true_and, and_true, true_or, or_true]
  split_ifs <;> first | (exfalso; omega) | skip
  rw [Real.cos_arctan, Real.sin_arctan]
  field_simp
  linear_combination (-1 : ℝ) * hS2

theorem iwaB_of_ne (s : ℝ) {i : Fin n} (h1 : i ≠ ia hr) (h2 : i ≠ ib hr) :
    iwaB hr s i i = 1 := by
  have h1' : (i : ℕ) ≠ r := fun h => h1 (Fin.ext h)
  have h2' : (i : ℕ) ≠ r + 1 := fun h => h2 (Fin.ext h)
  rw [iwaB_apply, blockRotation_apply hr]
  split_ifs <;> first | (exfalso; omega) | simp

theorem diagChar_iwaB (a : Fin n → ℂ) (e : Fin n → Fin 2) (s : ℝ) :
    diagChar a e (iwaB hr s) =
      (Real.sqrt (1 + s ^ 2) : ℂ) ^ (a (ib hr) - a (ia hr)) := by
  have hS := sqrt_one_add_sq_pos s
  have hS0 : (Real.sqrt (1 + s ^ 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  unfold diagChar
  rw [← Finset.prod_subset (Finset.subset_univ {ia hr, ib hr}) (fun i _ hi => ?_),
    Finset.prod_pair (ia_ne_ib hr), iwaB_ia, iwaB_ib, charFun_of_pos _ _ (by positivity),
    charFun_of_pos _ _ hS]
  · have harg : (Real.sqrt (1 + s ^ 2) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hS.le]
      exact Real.pi_ne_zero.symm
    rw [Complex.cpow_sub _ _ hS0, one_div, Complex.ofReal_inv, Complex.inv_cpow _ _ harg,
      inv_mul_eq_div]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [iwaB_of_ne hr s hi.1 hi.2, charFun_one]

end Iwasawa

/-! ## A test vector -/

section TestVector

/-- The parities `e` as a function on `ℕ`, `0` beyond `n`. -/
def pE (e : Fin n → Fin 2) : ℕ → ℕ := fun l => if h : l < n then (e ⟨l, h⟩).val else 0

theorem realPositionCharacter_map_character_of_le :
    ∀ (cs : List RealCharacterData) (l : ℕ), cs.length ≤ l → ∀ x : ℝˣ,
      realPositionCharacter (cs.map RealBlock.character) l x = 1
  | [], _, _, _ => rfl
  | c :: cs, 0, h, _ => by simp at h
  | c :: cs, l + 1, h, x => by
      simp only [List.map_cons, realPositionCharacter]
      exact realPositionCharacter_map_character_of_le cs l (by simpa using h) x

theorem PL_position_neg_one_pE (τ : Fin n → ℂ) (e : Fin n → Fin 2) (l : ℕ) :
    realPositionCharacter (PL τ e) l (-1) = (-1) ^ pE e l := by
  by_cases h : l < n
  · have := PL_position_neg_one τ e ⟨l, h⟩
    simpa [pE, h] using this
  · rw [PL, realPositionCharacter_map_character_of_le _ l (by simpa using h)]
    simp [pE, h]

theorem mem_KF_of_mem (τ : Fin n → ℂ) (e : Fin n → Fin 2) {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter (PL τ e)))
      (unitaryCompact ℝ n)) : f ∈ KF n (PL τ e) := by
  refine Submodule.mem_inf.mpr ⟨⟨hf.1, ?_⟩, hf.2⟩
  intro q d hd
  rw [PL, RealPrincipalSeriesDuality.realInducedBlockAt_map_character] at hd
  exact absurd hd (by simp)

theorem exists_testVector {r : ℕ} (hr : r + 1 < n) (τ : Fin n → ℂ) (e : Fin n → Fin 2) :
    ∃ f : KF n (PL τ e), ∀ θ : ℝ, (f : Langlands.GeneralLinear n ℝ → ℂ) (blockRotation n r θ) =
      (Real.cos θ : ℂ) ^ ((e (ia hr)).val + (e (ib hr)).val) := by
  obtain ⟨f, hf, hfK⟩ := principalSeriesExtension n (PL τ e)
    (JacquetNonvanishing.signMonomial n (pE e) 0)
    (JacquetNonvanishing.continuous_signMonomial _ _)
    (JacquetNonvanishing.finiteDimensional_signMonomial _ _)
    (JacquetNonvanishing.signMonomial_signDiagonal (pE e) 0 (PL_position_neg_one_pE τ e)
      (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _))
  refine ⟨⟨f, mem_KF_of_mem τ e hf⟩, fun θ => ?_⟩
  have hk := blockRotation_mem_unitaryCompact n r θ
  have hu : blockRotation n r θ = Unitary.toUnits (⟨(blockRotation n r θ :
      Matrix (Fin n) (Fin n) ℝ), hk⟩ : Matrix.unitaryGroup (Fin n) ℝ) := Units.ext rfl
  change f (blockRotation n r θ) = _
  have hd1 : (blockRotation n r θ : Matrix (Fin n) (Fin n) ℝ) (ia hr) (ia hr) = Real.cos θ := by
    rw [blockRotation_apply hr]
    simp [ia]
  have hd2 : (blockRotation n r θ : Matrix (Fin n) (Fin n) ℝ) (ib hr) (ib hr) = Real.cos θ := by
    rw [blockRotation_apply hr]
    simp [ib]
  have hp1 : pE e ((ia hr : Fin n) : ℕ) = (e (ia hr)).val := by simp [pE]
  have hp2 : pE e ((ib hr : Fin n) : ℕ) = (e (ib hr)).val := by simp [pE]
  rw [hu, hfK]
  show ∏ l : Fin n, (((blockRotation n r θ : Matrix (Fin n) (Fin n) ℝ) l l : ℝ) : ℂ) ^
      (pE e l) = _
  rw [← Finset.prod_subset (Finset.subset_univ {ia hr, ib hr}) (fun i _ hi => ?_),
    Finset.prod_pair (ia_ne_ib hr), hd1, hd2, hp1, hp2, ← pow_add]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  have h1' : (i : ℕ) ≠ r := fun h => hi.1 (Fin.ext h)
  have h2' : (i : ℕ) ≠ r + 1 := fun h => hi.2 (Fin.ext h)
  rw [blockRotation_apply hr]
  simp [h1', h2']

end TestVector

/-! ## Derivatives along the lower root group -/

section LowerRoot

open scoped Manifold ContDiff Matrix.Norms.Operator

variable {p : ℕ} (hp : p + 1 < n)

/-- `s ↦ F(e(s))` has derivative `(R(E) F)(e(t))` at `t`. -/
theorem hasDerivAt_lowerRoot {F : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ F) (t : ℝ) :
    HasDerivAt (fun s => F (lowerRootElement n p hp s))
      (rightDerivative (matrixModel ℝ n) (lowerRootMatrix n p hp) F
        (lowerRootElement n p hp t)) t := by
  have hfun : (fun s => F (lowerRootElement n p hp s)) =
      fun s => unitsExtension F (1 + s • lowerRootMatrix n p hp) := by
    funext s
    rw [← lowerRootElement_val, unitsExtension_val]
  rw [hfun, rightDerivative_eq_fderiv hF, lowerRootElement_val, add_mul, one_mul,
    smul_mul_assoc, lowerRootMatrix_mul_self, smul_zero, add_zero]
  have hd : HasDerivAt (fun s : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) + s • lowerRootMatrix n p hp)
      (lowerRootMatrix n p hp) t := by
    simpa using ((hasDerivAt_id t).smul_const (lowerRootMatrix n p hp)).const_add 1
  have hu : IsUnit (1 + t • lowerRootMatrix n p hp) := by
    rw [← lowerRootElement_val]
    exact Units.isUnit _
  exact (differentiableAt_unitsExtension hF hu).hasFDerivAt.comp_hasDerivAt t hd

/-- The iterated derivatives of `s ↦ F(e(s))` are the iterated right derivatives along `E`. -/
theorem iteratedDeriv_lowerRoot {F : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ F) (m : ℕ) :
    iteratedDeriv m (fun s => F (lowerRootElement n p hp s)) =
      fun t => ((rightDerivative (matrixModel ℝ n) (lowerRootMatrix n p hp))^[m] F)
        (lowerRootElement n p hp t) := by
  induction m generalizing F with
  | zero => rfl
  | succ m ih =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have hd : deriv (fun s => F (lowerRootElement n p hp s)) =
        fun t => rightDerivative (matrixModel ℝ n) (lowerRootMatrix n p hp) F
          (lowerRootElement n p hp t) :=
      funext fun t => (hasDerivAt_lowerRoot hp hF t).deriv
    rw [hd]
    exact ih (contMDiff_rightDerivative hF _)

end LowerRoot

/-! ## Nonvanishing of the block Jacquet functional -/

section Nonvanishing

variable {ds : List RealBlock} {r : ℕ} {μ : ℤ → ℂ} {e : Fin n → Fin 2}

/-- If `μ_j Φ_j(v)(1) ≠ 0` for some `v`, then `ℓ_μ ≠ 0`: otherwise the Frobenius function of
every `v` vanishes, and so do its block Fourier coefficients `μ_j Φ_j(v)`. -/
theorem blockJacquet_ne_zero (hr : r + 1 < n)
    (hsign : ∀ (i : Fin n) (v : KF n ds),
      blockJacquet n ds r μ (realStandardRep n ds (signReflection n i) v) =
        (-1) ^ (e i).val * blockJacquet n ds r μ v)
    {j : ℤ} (hμ : μ j ≠ 0) (v : KF n ds) (hv : blockFourierCoefficient n r j v 1 ≠ 0) :
    blockJacquet n ds r μ ≠ 0 := by
  intro h0
  have hF : RealJacquetFrobenius.frobFun (realStandardRep n ds) (blockJacquet n ds r μ) 0 e v =
      0 := by
    funext g
    simp [RealJacquetFrobenius.frobFun, h0]
  have h := blockFourierCoefficient_frobFun (a := 0) hr hsign v (one_mem (unitaryCompact ℝ n)) j
  rw [hF, blockFourierCoefficient_zero_fun] at h
  exact mul_ne_zero hμ hv h.symm

/-- The test vector has a nonzero block Fourier coefficient in the parity class `par`. -/
theorem exists_blockFourierCoefficient_par_ne_zero (hr : r + 1 < n) (τ : Fin n → ℂ)
    (e : Fin n → Fin 2) :
    ∃ f : KF n (PL τ e), blockFourierCoefficient n r (par hr e) f 1 ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_testVector hr τ e
  refine ⟨f, ?_⟩
  rw [blockFourierCoefficient_eq_coeff]
  simp_rw [mul_one, hf]
  have h1 := (e (ia hr)).isLt
  have h2 := (e (ib hr)).isLt
  exact coeff_cos_pow_ne_zero (by omega)

theorem blockJacquet_PL_ne_zero (hr : r + 1 < n) (τ : Fin n → ℂ) (e : Fin n → Fin 2)
    {e' : Fin n → Fin 2}
    (hsign : ∀ (i : Fin n) (v : KF n (PL τ e)),
      blockJacquet n (PL τ e) r μ (realStandardRep n (PL τ e) (signReflection n i) v) =
        (-1) ^ (e' i).val * blockJacquet n (PL τ e) r μ v)
    (hμ : μ (par hr e) ≠ 0) : blockJacquet n (PL τ e) r μ ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_blockFourierCoefficient_par_ne_zero hr τ e
  exact blockJacquet_ne_zero hr hsign hμ f hf

end Nonvanishing

/-! ## The `k`-th power of the lower root vector -/

section LowerPower

open scoped Manifold ContDiff Matrix.Norms.Operator
open Polynomial

/-- The modes `k - 1 - 2b`, `b < k`, of a function of degree `k - 1`. -/
def jIdx (k b : ℕ) : ℤ := (k : ℤ) - 1 - 2 * (b : ℤ)

theorem finsum_eq_sum_jIdx {k : ℕ} (F : ℤ → ℂ)
    (hF : ∀ j, F j ≠ 0 → |j| < k ∧ Even ((k : ℤ) - 1 - j)) :
    ∑ᶠ j, F j = ∑ b ∈ Finset.range k, F (jIdx k b) := by
  rw [finsum_eq_sum_of_support_subset F (s := (Finset.range k).image (jIdx k)),
    Finset.sum_image]
  · intro b1 _ b2 _ h
    unfold jIdx at h
    omega
  · intro j hj
    obtain ⟨hlt, c, hc⟩ := hF j hj
    rw [abs_lt] at hlt
    have hc0 : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg (by omega)
    rw [Finset.coe_image]
    refine ⟨c.toNat, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), ?_⟩
    unfold jIdx
    omega

variable {ds : List RealBlock} {r : ℕ} {μ : ℤ → ℂ} {a : Fin n → ℂ} {e : Fin n → Fin 2}

/-- On the lower root group: `B v (e(s)) = χ(b(s)) B v (r_p(arctan s))`. -/
theorem frobFun_lowerRoot (hr : r + 1 < n)
    (hsign : ∀ (i : Fin n) (v : KF n ds),
      blockJacquet n ds r μ (realStandardRep n ds (signReflection n i) v) =
        (-1) ^ (e i).val * blockJacquet n ds r μ v)
    (v : KF n ds) (s : ℝ) :
    RealJacquetFrobenius.frobFun (realStandardRep n ds) (blockJacquet n ds r μ) a e v
        (lowerRootElement n r hr s) =
      diagChar a e (iwaB hr s) *
        RealJacquetFrobenius.frobFun (realStandardRep n ds) (blockJacquet n ds r μ) a e v
          (blockRotation n r (Real.arctan s)) := by
  have hk := blockRotation_mem_unitaryCompact n r (Real.arctan s)
  rw [RealJacquetFrobenius.frobFun_eq hsign (b := iwaB hr s)
      (k := (blockRotation n r (Real.arctan s) : Matrix (Fin n) (Fin n) ℝ))
      (iwaB_upper hr s) hk (iwaB_mul hr s) v,
    RealJacquetFrobenius.frobFun_eq hsign (b := 1)
      (k := (blockRotation n r (Real.arctan s) : Matrix (Fin n) (Fin n) ℝ))
      Matrix.blockTriangular_one hk (one_mul _).symm v,
    diagChar_one, one_mul]

/-- On the rotations of the block: `B v (r_p(θ)) = (2π)⁻¹ Σᶠ_i μ_i e^{iθ i} Φ_i(v)(1)`. -/
theorem frobFun_rotation (hr : r + 1 < n)
    (hsign : ∀ (i : Fin n) (v : KF n ds),
      blockJacquet n ds r μ (realStandardRep n ds (signReflection n i) v) =
        (-1) ^ (e i).val * blockJacquet n ds r μ v)
    (v : KF n ds) (θ : ℝ) :
    RealJacquetFrobenius.frobFun (realStandardRep n ds) (blockJacquet n ds r μ) a e v
        (blockRotation n r θ) =
      (2 * (Real.pi : ℂ))⁻¹ * ∑ᶠ i : ℤ, μ i * (Complex.exp ((i : ℂ) * (θ : ℂ) * Complex.I) *
        blockFourierCoefficient n r i v 1) := by
  rw [frobFun_apply_of_mem hsign v (blockRotation_mem_unitaryCompact n r θ)]
  congr 2
  funext i
  have h := blockFourierCoefficient_blockRotation_mul hr (v : Langlands.GeneralLinear n ℝ → ℂ) i θ 1
  rw [mul_one] at h
  rw [h]

/-- **The `k`-th power of `E_{r+1,r}`.** If the modes `j` with `μ_j Φ_j ≠ 0` satisfy `|j| < k`
and `j ≡ k - 1 (mod 2)`, and `a_r - a_{r+1} = 1 - k`, then `ℓ_μ ∘ π(E_{r+1,r})^k = 0`: on the
lower root group the Frobenius function is a polynomial of degree `< k`. -/
theorem blockJacquet_pow_eq_zero (hr : r + 1 < n)
    (hJ : IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds)
      (blockJacquet n ds r μ) a e)
    {k : ℕ} (hk : 1 ≤ k) (ha : a (ia hr) - a (ib hr) = 1 - (k : ℂ))
    (hwin : ∀ (j : ℤ) (f : KF n ds), μ j * blockFourierCoefficient n r j f 1 ≠ 0 →
      |j| < k ∧ Even ((k : ℤ) - 1 - j))
    (v : KF n ds) :
    blockJacquet n ds r μ ((realStandardLie n ds (1 ⊗ₜ lowerRootMatrix n r hr) ^ k) v) = 0 := by
  have hgk := isRealGKModule_realStandardModule n ds
  have hsign : ∀ (i : Fin n) (w : KF n ds),
      blockJacquet n ds r μ (realStandardRep n ds (signReflection n i) w) =
        (-1) ^ (e i).val * blockJacquet n ds r μ w := fun i w => (hJ.2 i w).2
  have hF : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞
      (RealJacquetFrobenius.frobFun (realStandardRep n ds) (blockJacquet n ds r μ) a e v) :=
    contMDiff_frobFun hsign hgk.1 hgk.2.1 v
  have hexp : a (ib hr) - a (ia hr) = ((k - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub hk]
    push_cast
    linear_combination -ha
  have hpoly : ∃ q : ℂ[X], q.natDegree < k ∧ ∀ s : ℝ,
      RealJacquetFrobenius.frobFun (realStandardRep n ds) (blockJacquet n ds r μ) a e v
        (lowerRootElement n r hr s) = q.eval (s : ℂ) := by
    set q : ℂ[X] := ∑ b ∈ Finset.range k,
      C ((2 * (Real.pi : ℂ))⁻¹ * (μ (jIdx k b) * blockFourierCoefficient n r (jIdx k b) v 1)) *
        ((C Complex.I * X + C 1) ^ (k - 1 - b) * (C (-Complex.I) * X + C 1) ^ b) with hqdef
    refine ⟨q, ?_, fun s => ?_⟩
    · have hle : q.natDegree ≤ k - 1 := by
        rw [hqdef]
        refine natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
        have hb' : b < k := Finset.mem_range.mp hb
        refine (natDegree_mul_le_of_le (natDegree_C _).le (natDegree_mul_le_of_le
          (natDegree_pow_le_of_le _ natDegree_linear_le)
          (natDegree_pow_le_of_le _ natDegree_linear_le))).trans ?_
        omega
      omega
    · rw [frobFun_lowerRoot hr hsign v s, diagChar_iwaB, frobFun_rotation hr hsign v,
        finsum_eq_sum_jIdx _ fun j hj => hwin j v fun h0 => hj (by
          rw [mul_left_comm, h0, mul_zero]),
        hexp, Complex.cpow_natCast, hqdef]
      simp only [eval_finsetSum, eval_mul, eval_pow, eval_add, eval_C, eval_X]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb' : b < k := Finset.mem_range.mp hb
      rw [pow_mul_pow_eq s (k - 1 - b) b (jIdx k b) (by unfold jIdx; omega),
        show k - 1 - b + b = k - 1 by omega]
      ring
  obtain ⟨q, hdeg, hq⟩ := hpoly
  have hfun : (fun s => RealJacquetFrobenius.frobFun (realStandardRep n ds)
      (blockJacquet n ds r μ) a e v (lowerRootElement n r hr s)) =
      fun s : ℝ => q.eval (s : ℂ) := funext hq
  rw [← frobFun_apply_one (a := a) hsign, ← iterate_rightDerivative_frobFun hgk hJ]
  have h1 := congrFun (iteratedDeriv_lowerRoot hr hF k) 0
  simp only [lowerRootElement_zero'] at h1
  rw [← h1, hfun]
  exact iteratedDeriv_eval_eq_zero hdeg 0

end LowerPower

/-! ## The linked adjacent crossing -/

section Linked

/-- **Linked adjacent pair.** If `τ_r - τ_{r+1} = k > 0` and `k + e_r + e_{r+1}` is odd, the block
Jacquet functional of the binomial multiplier at `r` gives the conclusion for `PL τ e`. -/
theorem concl_of_linked_adjacent {r : ℕ} (hr : r + 1 < n) (τ : Fin n → ℂ) (e : Fin n → Fin 2)
    {k : ℕ} (hk : 0 < k) (hτ : τ (ia hr) - τ (ib hr) = k)
    (hodd : Odd (k + (e (ia hr)).val + (e (ib hr)).val)) : Concl n (PL τ e) := by
  set ε : ℤ := ((par hr e : ℕ) : ℤ) with hεdef
  have hε : ε = 0 ∨ ε = 1 := par_cases hr e
  have hpar : Even ((k : ℤ) - 1 - ε) := by
    rw [hεdef, Int.even_iff]
    unfold par
    obtain ⟨m, hm⟩ := hodd
    omega
  set μ := binomialMultiplier k ε with hμdef
  have hrec : IsRecurrent (τ (ia hr) - τ (ib hr) + 1) (par hr e) μ := by
    rw [hτ]
    exact isRecurrent_binomialMultiplier hk hε hpar
  have hsym : IsSymmetric (par hr e) ((-1) ^ par hr e) μ :=
    isSymmetric_binomialMultiplier k hε
  have hJ := isJacquet_cross hr τ e hrec hsym
  have hsign : ∀ (i : Fin n) (v : KF n (PL τ e)),
      blockJacquet n (PL τ e) r μ (realStandardRep n (PL τ e) (signReflection n i) v) =
        (-1) ^ ((e ∘ sw hr) i).val * blockJacquet n (PL τ e) r μ v := fun i v => (hJ.2 i v).2
  have ha : crossExp hr τ (ia hr) - crossExp hr τ (ib hr) = 1 - (k : ℂ) := by
    rw [crossExp_sub]
    linear_combination -hτ
  have hwin : ∀ (j : ℤ) (f : KF n (PL τ e)), μ j * blockFourierCoefficient n r j f 1 ≠ 0 →
      |j| < k ∧ Even ((k : ℤ) - 1 - j) := by
    intro j f h
    have hj : Even (j - ε) := by
      by_contra hj
      exact h (by rw [blockFourierCoefficient_eq_zero_of_not_even hr (PL_parity hr τ e) f hj 1,
        mul_zero])
    refine ⟨(binomialMultiplier_ne_zero_iff hk hε hpar hj).mp (left_ne_zero_of_mul h), ?_⟩
    rw [Int.even_iff] at hj hpar ⊢
    omega
  refine ⟨blockJacquet n (PL τ e) r μ, crossExp hr τ, e ∘ sw hr, r, k, hr, ?_, hJ, ha,
    blockJacquet_pow_eq_zero hr hJ hk ha hwin⟩
  refine blockJacquet_PL_ne_zero hr τ e hsign ?_
  refine (binomialMultiplier_ne_zero_iff (k := ε) hk hε hpar (by rw [sub_self]; exact Even.zero)).mpr ?_
  rw [Int.even_iff] at hpar
  rw [abs_lt]
  omega

end Linked

/-! ## Assembly: from a linked pair in Langlands order to a linked adjacent pair -/

section Assembly

open RealStrictCharacterLanglandsQuotient (IsCharacterList)

/-- The characters of `PL τ e` at the positions `i, j` are linked (Mœglin's condition (i), as in
`MoeglinDatum.IsLinked`): `τ_i - τ_j` is a nonzero integer `k` with `k + e_i + e_j` odd. -/
def Lk (τ : Fin n → ℂ) (e : Fin n → Fin 2) (i j : Fin n) : Prop :=
  ∃ k : ℤ, k ≠ 0 ∧ τ i - τ j = k ∧ Odd (k + ((e i).val : ℤ) + ((e j).val : ℤ))

/-- A linked adjacent pair with `re τ_{r+1} ≤ re τ_r` gives the conclusion. -/
theorem concl_of_lk_adjacent {r : ℕ} (hr : r + 1 < n) (τ : Fin n → ℂ) (e : Fin n → Fin 2)
    (hL : Lk τ e (ia hr) (ib hr)) (hre : (τ (ib hr)).re ≤ (τ (ia hr)).re) :
    Concl n (PL τ e) := by
  obtain ⟨k, hk0, hk, hodd⟩ := hL
  have hkre : (k : ℝ) = (τ (ia hr)).re - (τ (ib hr)).re := by
    have := congrArg Complex.re hk
    rw [Complex.sub_re, Complex.intCast_re] at this
    exact this.symm
  have hkpos : 0 < k := by
    have h1 : (0 : ℝ) ≤ k := by rw [hkre]; linarith
    have h2 : (0 : ℤ) ≤ k := by exact_mod_cast h1
    omega
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m := ⟨k.toNat, (Int.toNat_of_nonneg hkpos.le).symm⟩
  refine concl_of_linked_adjacent hr τ e (k := m) (by omega) (by rw [hk]; norm_cast) ?_
  have h3 : Odd ((m + (e (ia hr)).val + (e (ib hr)).val : ℕ) : ℤ) := by push_cast; exact hodd
  exact (Int.odd_coe_nat _).mp h3

/-- **Reduction to an adjacent pair.** Induction on the gap `d = j - i - 1`: if the pair
`(j - 1, j)` is linked it is the adjacent pair; otherwise the generic crossing at `j - 1` moves
the character at `j` to `j - 1`. -/
theorem concl_of_lk (d : ℕ) : ∀ (τ : Fin n → ℂ) (e : Fin n → Fin 2) (i j : Fin n),
    (j : ℕ) = i + d + 1 → Lk τ e i j → (τ j).re ≤ (τ i).re →
      (∀ m : Fin n, i < m → m < j → (τ j).re ≤ (τ m).re) → Concl n (PL τ e) := by
  induction d with
  | zero =>
    rintro τ e ⟨i, hi⟩ ⟨j, hj⟩ hji hL hre -
    simp only [add_zero] at hji
    subst hji
    exact concl_of_lk_adjacent hj τ e hL hre
  | succ d ih =>
    rintro τ e ⟨i, hi⟩ ⟨j, hj⟩ hji hL hre hmid
    simp only at hji
    obtain ⟨r, rfl⟩ : ∃ r, j = r + 1 := ⟨j - 1, by omega⟩
    have hr : r + 1 < n := hj
    have hra : (⟨i, hi⟩ : Fin n) < ia hr := by
      rw [Fin.lt_def]
      simp only [ia]
      omega
    have hrb : ia hr < (⟨r + 1, hj⟩ : Fin n) := by
      rw [Fin.lt_def]
      simp only [ia]
      omega
    have hre' : (τ (ib hr)).re ≤ (τ (ia hr)).re := hmid (ia hr) hra hrb
    by_cases hL' : Lk τ e (ia hr) (ib hr)
    · exact concl_of_lk_adjacent hr τ e hL' hre'
    · refine concl_of_generic hr τ e (by rw [Complex.sub_re]; linarith) ?_ ?_
      · intro m hm
        apply hL'
        refine ⟨((par hr e : ℕ) : ℤ) + 2 * m + 1, by omega, by rw [hm]; push_cast; ring, ?_⟩
        rw [Int.odd_iff]
        unfold par
        omega
      · have hia : (⟨i, hi⟩ : Fin n) ≠ ia hr := ne_of_lt hra
        have hib : (⟨i, hi⟩ : Fin n) ≠ ib hr := by
          rw [Ne, Fin.ext_iff]
          simp only [ib]
          omega
        have hsi : sw hr ⟨i, hi⟩ = ⟨i, hi⟩ := sw_of_ne hr hia hib
        refine ih (τ ∘ sw hr) (e ∘ sw hr) ⟨i, hi⟩ (ia hr) (by simp only [ia]; omega) ?_ ?_ ?_
        · simp only [Lk, Function.comp_apply, hsi, sw_ia]
          exact hL
        · simp only [Function.comp_apply, hsi, sw_ia]
          exact hre
        · intro m him hmr
          have hma : m ≠ ia hr := ne_of_lt hmr
          have hmb : m ≠ ib hr := by
            rw [Ne, Fin.ext_iff]
            rw [Fin.lt_def] at hmr
            simp only [ia] at hmr
            simp only [ib]
            omega
          simp only [Function.comp_apply, sw_of_ne hr hma hmb, sw_ia]
          exact hmid m him (lt_trans hmr hrb)

/-- The Mœglin data of a list of real characters. -/
theorem realMoeglinData_map_character (l : List RealCharacterData) :
    realMoeglinData (l.map RealBlock.character) =
      l.map fun c => MoeglinDatum.character c.parity c.exponent := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.map_cons, List.map_cons, ← ih]
    simp [realMoeglinData, realBlockMoeglinData]

/-- **The character case for `PL τ e`.** -/
theorem concl_of_char (τ : Fin n → ℂ) (e : Fin n → Fin 2)
    (hord : IsRealLanglandsOrdered (PL τ e)) (hlink : ¬ IsRealMoeglinUnlinked (PL τ e)) :
    Concl n (PL τ e) := by
  have hord1 : ((List.ofFn fun i => charData (e i) (τ i)).map RealBlock.character).Pairwise
      (fun x y => realBlockExponent y ≤ realBlockExponent x) := hord
  have hord' : ∀ i j : Fin n, i < j → (τ j).re ≤ (τ i).re := fun i j hij =>
    List.pairwise_ofFn.mp (List.pairwise_map.mp hord1) hij
  have hlink1 : ¬ (realMoeglinData (PL τ e)).Pairwise fun a b => ¬ a.IsLinked b := hlink
  rw [PL, realMoeglinData_map_character, List.map_ofFn, List.pairwise_ofFn] at hlink1
  push Not at hlink1
  obtain ⟨i, j, hij, hL⟩ := hlink1
  have hij' : (i : ℕ) < j := hij
  exact concl_of_lk ((j : ℕ) - i - 1) τ e i j (by omega) hL (hord' i j hij)
    fun m _ hm => hord' m j hm

/-- `charData` of the parity and exponent of a real character datum is the datum. -/
theorem charData_eta (c : RealCharacterData) : charData c.parity c.exponent = c := by
  obtain ⟨χ, ε, t, h⟩ := c
  have hχ : charHom ε t = χ := by
    ext x
    change charFun ε t x = _
    rw [h x]
    rfl
  subst hχ
  rfl

/-- A list of real characters is the image of a list of real character data. -/
theorem exists_eq_map_character {ds : List RealBlock} (h : IsCharacterList ds) :
    ∃ cs : List RealCharacterData, ds = cs.map RealBlock.character := by
  induction ds with
  | nil => exact ⟨[], rfl⟩
  | cons b ds ih =>
    obtain ⟨c, rfl⟩ := h b (by simp)
    obtain ⟨cs, rfl⟩ := ih fun b hb => h b (by simp [hb])
    exact ⟨c :: cs, rfl⟩

end Assembly

end RealCharacterCrossing

open Langlands.LocalFactor.Archimedean RealCharacterCrossing in
/-- **S2 for lists of real characters** (`RealCharacterLinkedJacquetFunctionalStatement`). -/
theorem realCharacterLinkedJacquetFunctional : RealCharacterLinkedJacquetFunctionalStatement := by
  intro n ds hrank hc hord hlink
  obtain ⟨cs, rfl⟩ := exists_eq_map_character hc
  have hlen : cs.length = n := by rw [← hrank, realRank_map_character]
  subst hlen
  have hPL : cs.map RealBlock.character =
      PL (fun i => cs[(i : ℕ)].exponent) (fun i => cs[(i : ℕ)].parity) := by
    rw [PL]
    congr 1
    conv_lhs => rw [← List.ofFn_getElem (xs := cs)]
    congr 1
    funext i
    exact (charData_eta _).symm
  rw [hPL] at hord hlink ⊢
  exact concl_of_char _ _ hord hlink

end Langlands.Archimedean
