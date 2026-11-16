import Langlands.Representation.Archimedean.ComplexGLTwoModel

/-!
# The algebraic core of the irreducibility of `GL_2(ℂ)` principal series

Assume that every `U(2)`-finite function of the standard module of `ds` (of length `2`) is
`realize Φ (s_J) P` for some level `J` and some `P ∈ Eig a_J b_J`, where
`a_j = m₀⁺ + j`, `b_j = m₀⁻ + j` and `s_j = A - a_j` (`Setup.hF1`). If `s_j ≠ 0` for all `j`
(`Setup.hup`) and `A + b_j + 1 ≠ 0` for all `j ≥ 1` (`Setup.hdown`), every nonzero subspace
stable under `complexStandardLie 2 ds` is everything (`Setup.eq_top`).
-/

noncomputable section

open MvPolynomial
open scoped TensorProduct

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.GLTwoCore

attribute [local instance 100] LieRing.ofAssociativeRing

open GLTwoPoly GLTwoModel

/-- The `z`-degree `a_j = m₀⁺ + j` at level `j`. -/
def la (m0 : ℤ) (j : ℕ) : ℕ := m0.toNat + j

/-- The `w`-degree `b_j = m₀⁻ + j` at level `j`. -/
def lb (m0 : ℤ) (j : ℕ) : ℕ := (-m0).toNat + j

/-- The exponent `s_j = A - a_j` of `|r|²` at level `j`. -/
def ls (A : ℂ) (m0 : ℤ) (j : ℕ) : ℂ := A - (la m0 j : ℂ)

theorem la_succ (m0 : ℤ) (j : ℕ) : (la m0 (j + 1) : ℂ) = (la m0 j : ℂ) + 1 := by
  simp [la]; ring

theorem lb_succ (m0 : ℤ) (j : ℕ) : (lb m0 (j + 1) : ℂ) = (lb m0 j : ℂ) + 1 := by
  simp [lb]; ring

theorem ls_succ (A : ℂ) (m0 : ℤ) (j : ℕ) : ls A m0 (j + 1) = ls A m0 j - 1 := by
  simp [ls, la]; ring

/-- The hypotheses of the algebraic irreducibility argument. -/
structure Setup (ds : List LocalFactor.Archimedean.ComplexCharacterData) (Φ : ℂ → ℂ) (A : ℂ)
    (m0 : ℤ) : Prop where
  hΦ : ∀ δ : ℂ, δ ≠ 0 → DifferentiableAt ℝ Φ δ
  hΦ0 : ∀ δ : ℂ, δ ≠ 0 → Φ δ ≠ 0
  hF1 : ∀ x : KF2 ds, ∃ (J : ℕ) (P : Pol), P ∈ Eig (la m0 J) (lb m0 J) ∧
    IsRealized Φ (ls A m0 J) P x
  hup : ∀ j : ℕ, ls A m0 j ≠ 0
  hdown : ∀ j : ℕ, 1 ≤ j → A + (lb m0 j : ℂ) + 1 ≠ 0

variable {ds : List LocalFactor.Archimedean.ComplexCharacterData} {Φ : ℂ → ℂ} {A : ℂ} {m0 : ℤ}

/-- The polynomials realized at level `j` by elements of `W`. -/
def lev (Φ : ℂ → ℂ) (A : ℂ) (m0 : ℤ) (W : Submodule ℂ (KF2 ds)) (j : ℕ) : Submodule ℂ Pol where
  carrier := {P | ∃ x ∈ W, IsRealized Φ (ls A m0 j) P x}
  zero_mem' := ⟨0, W.zero_mem, isRealized_zero Φ _⟩
  add_mem' := by
    rintro P Q ⟨x, hx, hPx⟩ ⟨y, hy, hQy⟩
    refine ⟨x + y, W.add_mem hx hy, ?_⟩
    rw [Submodule.coe_add]
    exact hPx.add hQy
  smul_mem' := by
    rintro c P ⟨x, hx, hPx⟩
    refine ⟨c • x, W.smul_mem c hx, ?_⟩
    rw [Submodule.coe_smul, smul_eq_C_mul]
    exact hPx.smul c

theorem mem_lev {W : Submodule ℂ (KF2 ds)} {j : ℕ} {P : Pol} :
    P ∈ lev Φ A m0 W j ↔ ∃ x ∈ W, IsRealized Φ (ls A m0 j) P x := Iff.rfl

theorem casOp_mem {W : Submodule ℂ (KF2 ds)}
    (hW : ∀ (Y : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ), ∀ x ∈ W, complexStandardLie 2 ds Y x ∈ W)
    {x : KF2 ds} (hx : x ∈ W) : casOp ds x ∈ W := by
  simp only [casOp, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply]
  exact W.add_mem (W.add_mem (W.smul_of_tower_mem 2 (hW _ _ (hW _ _ hx)))
    (W.smul_of_tower_mem 2 (hW _ _ (hW _ _ hx)))) (hW _ _ (hW _ _ hx))

/-- One application of `casOp - casValue`: a level `j + 1` vector goes to level `j`. -/
theorem isRealized_cas_sub (S : Setup ds Φ A m0) {j : ℕ} {P : Pol}
    (hP : P ∈ Eig (la m0 (j + 1)) (lb m0 (j + 1))) {x : KF2 ds}
    (hx : IsRealized Φ (ls A m0 (j + 1)) P x) :
    IsRealized Φ (ls A m0 j) (C (-4) * Lap P)
      ((casOp ds x - casValue (la m0 (j + 1)) (lb m0 (j + 1)) • x : KF2 ds) :
        Langlands.GeneralLinear 2 ℂ → ℂ) := by
  have h1 := isRealized_casOp S.hΦ hx
  rw [Cas_eq hP] at h1
  have h2 := h1.sub (hx.smul (casValue (la m0 (j + 1)) (lb m0 (j + 1))))
  rw [Submodule.coe_sub, Submodule.coe_smul]
  have e : C (casValue (la m0 (j + 1)) (lb m0 (j + 1))) * P - 4 * (N * Lap P) -
      C (casValue (la m0 (j + 1)) (lb m0 (j + 1))) * P = N * (C (-4) * Lap P) := by
    rw [map_neg, map_ofNat]; ring
  rw [e] at h2
  exact h2.of_N_mul.congr_exp (by rw [ls_succ]; ring)

theorem lap_mem_succ {j : ℕ} {P : Pol} (hP : P ∈ Eig (la m0 (j + 1)) (lb m0 (j + 1))) :
    C (-4) * Lap P ∈ Eig (la m0 j) (lb m0 j) := by
  have h := Lap_mem hP
  rw [la_succ, lb_succ, add_sub_cancel_right, add_sub_cancel_right] at h
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ h

theorem C_mul_ne_zero {c : ℂ} {Q : Pol} (hc : c ≠ 0) (hQ : Q ≠ 0) : C c * Q ≠ 0 :=
  mul_ne_zero (by simpa using hc) hQ

section Descent

variable (S : Setup ds Φ A m0) {W : Submodule ℂ (KF2 ds)}
  (hW : ∀ (Y : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ), ∀ x ∈ W, complexStandardLie 2 ds Y x ∈ W)

include hW in
theorem cas_sub_mem {x : KF2 ds} (hx : x ∈ W) (c : ℂ) : casOp ds x - c • x ∈ W :=
  W.sub_mem (casOp_mem hW hx) (W.smul_mem c hx)

include S in
theorem eq_zero_of_isRealized {s : ℂ} {Q : Pol} {x : KF2 ds} (hx : IsRealized Φ s Q x)
    (h0 : x = 0) : Q = 0 := by
  subst h0
  exact eq_zero_of_isRealized_zero S.hΦ0 hx

include S in
theorem ne_zero_of_isRealized {s : ℂ} {Q : Pol} {x : KF2 ds} (hx : IsRealized Φ s Q x)
    (hQ : Q ≠ 0) : x ≠ 0 := fun h0 => hQ (eq_zero_of_isRealized S hx h0)

include S hW in
/-- Two applications of `casOp - casValue` take a level `J + 2` vector of `W` to level `J`. -/
theorem two_step {J : ℕ} {Q : Pol} (hQ : Q ∈ Eig (la m0 (J + 2)) (lb m0 (J + 2))) {y : KF2 ds}
    (hyW : y ∈ W) (hy : IsRealized Φ (ls A m0 (J + 2)) Q y) :
    ∃ y' ∈ W, IsRealized Φ (ls A m0 J) (C (-4) * Lap (C (-4) * Lap Q)) y' ∧
      C (-4) * Lap (C (-4) * Lap Q) ∈ Eig (la m0 J) (lb m0 J) := by
  have h1 := isRealized_cas_sub S hQ hy
  have hm1 := lap_mem_succ hQ
  have h2 := isRealized_cas_sub S hm1 h1
  exact ⟨_, cas_sub_mem hW (cas_sub_mem hW hyW _) _, h2, lap_mem_succ hm1⟩

include S hW in
/-- **The down move.** A nonzero harmonic vector at level `J + 1` of `W` produces a nonzero
vector of `W` at level `J`. -/
theorem down_move {J : ℕ} {x : KF2 ds} (hxW : x ∈ W) {P : Pol}
    (hP : P ∈ Eig (la m0 (J + 1)) (lb m0 (J + 1))) (hx : IsRealized Φ (ls A m0 (J + 1)) P x)
    (hΔ : Lap P = 0) (hP0 : P ≠ 0) :
    ∃ y ∈ W, y ≠ 0 ∧ ∃ Q ∈ Eig (la m0 J) (lb m0 J), IsRealized Φ (ls A m0 J) Q y := by
  set s := ls A m0 (J + 1) with hs
  have hc : (2 * (s + (la m0 (J + 1) : ℂ) + (lb m0 (J + 1) : ℂ) + 1)) ≠ 0 := by
    have := S.hdown (J + 1) (by omega)
    rw [hs, ls]
    intro h
    apply this
    linear_combination h / 2
  have hmem : ∀ i k : Fin 2,
      holMove s i k P ∈ Eig (la m0 (J + 2)) (lb m0 (J + 2)) := by
    intro i k
    have := holMove_mem hP s i k
    rwa [← la_succ, ← lb_succ] at this
  have hexp : s - 1 = ls A m0 (J + 2) := by simp only [hs, ls, la]; push_cast; ring
  -- the three holomorphic moves
  have r01 : IsRealized Φ (ls A m0 (J + 2)) (holMove s 0 1 P)
      (complexStandardLie 2 ds (hol E01) x) := by
    have h := isRealized_hol S.hΦ hx E01 trace_E01
    rw [holZ_E01, holT_E01, hexp] at h
    have e : holMove s 0 1 P = C s * (w 1 * z 0 * P) + N * (z 0 * dz 1 P) := by
      rw [holMove]; ring
    rw [e]; exact h
  have r10 : IsRealized Φ (ls A m0 (J + 2)) (holMove s 1 0 P)
      (complexStandardLie 2 ds (hol E10) x) := by
    have h := isRealized_hol S.hΦ hx E10 trace_E10
    rw [holZ_E10, holT_E10, hexp] at h
    have e : holMove s 1 0 P = C s * (w 0 * z 1 * P) + N * (z 1 * dz 0 P) := by
      rw [holMove]; ring
    rw [e]; exact h
  have rd : IsRealized Φ (ls A m0 (J + 2)) (holMove s 0 0 P - holMove s 1 1 P)
      (complexStandardLie 2 ds (hol Ed) x) := by
    have h := isRealized_hol S.hΦ hx Ed trace_Ed
    rw [holZ_Ed, holT_Ed, hexp] at h
    have e : holMove s 0 0 P - holMove s 1 1 P =
        C s * ((w 0 * z 0 - w 1 * z 1) * P) + N * (z 0 * dz 0 P - z 1 * dz 1 P) := by
      rw [holMove, holMove]; ring
    rw [e]; exact h
  have key : ∀ Q : Pol, Lap (Lap Q) ≠ 0 → Q ∈ Eig (la m0 (J + 2)) (lb m0 (J + 2)) →
      ∀ y : KF2 ds, y ∈ W → IsRealized Φ (ls A m0 (J + 2)) Q y →
        ∃ y ∈ W, y ≠ 0 ∧ ∃ Q ∈ Eig (la m0 J) (lb m0 J), IsRealized Φ (ls A m0 J) Q y := by
    intro Q hQ0 hQ y hyW hy
    obtain ⟨y', hy'W, hy', hm⟩ := two_step S hW hQ hyW hy
    refine ⟨y', hy'W, ne_zero_of_isRealized S hy' ?_, _, hm, hy'⟩
    rw [Lap_C_mul, ← mul_assoc, ← map_mul]
    exact C_mul_ne_zero (by norm_num) hQ0
  have hLL : ∀ i k : Fin 2, Lap (Lap (holMove s i k P)) =
      C (2 * (s + (la m0 (J + 1) : ℂ) + (lb m0 (J + 1) : ℂ) + 1)) * dz k (dw i P) :=
    fun i k => Lap_Lap_holMove hP hΔ s i k
  have hla : (la m0 (J + 1) : ℂ) ≠ 0 := by rw [Nat.cast_ne_zero]; simp [la]
  have hlb : (lb m0 (J + 1) : ℂ) ≠ 0 := by rw [Nat.cast_ne_zero]; simp [lb]
  rcases exists_traceless_ne_zero hP hΔ hla hlb hP0 with h | h | h
  · refine key _ ?_ (hmem 0 1) _ (hW _ _ hxW) r01
    rw [hLL]; exact C_mul_ne_zero hc h
  · refine key _ ?_ (hmem 1 0) _ (hW _ _ hxW) r10
    rw [hLL]; exact C_mul_ne_zero hc h
  · refine key _ ?_ (sub_mem (hmem 0 0) (hmem 1 1)) _ (hW _ _ hxW) rd
    rw [Lap_sub, Lap_sub, hLL, hLL, ← mul_sub]
    exact C_mul_ne_zero hc h

include S hW in
/-- **Descent.** A nonzero vector of `W` at any level produces a nonzero vector of `W` at
level `0`. -/
theorem descent (J : ℕ) {x : KF2 ds} (hxW : x ∈ W) (hx0 : x ≠ 0) {P : Pol}
    (hP : P ∈ Eig (la m0 J) (lb m0 J)) (hx : IsRealized Φ (ls A m0 J) P x) :
    ∃ y ∈ W, y ≠ 0 ∧ ∃ Q ∈ Eig (la m0 0) (lb m0 0), IsRealized Φ (ls A m0 0) Q y := by
  induction J using Nat.strong_induction_on generalizing x P with
  | _ J ih =>
    rcases J with _ | J
    · exact ⟨x, hxW, hx0, P, hP, hx⟩
    · have hP0 : P ≠ 0 := by
        rintro rfl
        exact hx0 (Subtype.ext ((isRealized_zero Φ _).unique hx).symm)
      have h1 := isRealized_cas_sub S hP hx
      have hy := cas_sub_mem hW hxW (casValue (la m0 (J + 1)) (lb m0 (J + 1)))
      by_cases hy0 : casOp ds x - casValue (la m0 (J + 1)) (lb m0 (J + 1)) • x = 0
      · have hL := eq_zero_of_isRealized S h1 hy0
        have hΔ : Lap P = 0 := by
          rcases mul_eq_zero.mp hL with h | h
          · exact absurd h (by simp)
          · exact h
        obtain ⟨y, hyW, hy0', Q, hQ, hyQ⟩ := down_move S hW hxW hP hx hΔ hP0
        exact ih J (by omega) hyW hy0' hQ hyQ
      · exact ih J (by omega) hy hy0 (lap_mem_succ hP) h1

include S hW in
/-- **The bottom level.** A nonzero vector of `W` at level `0` gives all of level `0`. -/
theorem bottom {y : KF2 ds} (hyW : y ∈ W) (hy0 : y ≠ 0) {Q : Pol}
    (hQ : Q ∈ Eig (la m0 0) (lb m0 0)) (hy : IsRealized Φ (ls A m0 0) Q y) :
    Eig (la m0 0) (lb m0 0) ≤ lev Φ A m0 W 0 := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hy0 (Subtype.ext ((isRealized_zero Φ _).unique hy).symm)
  have hV0 : lev Φ A m0 W 0 ⊓ Eig (la m0 0) (lb m0 0) ≠ ⊥ := by
    intro h
    apply hQ0
    have hmem : Q ∈ lev Φ A m0 W 0 ⊓ Eig (la m0 0) (lb m0 0) := ⟨⟨y, hyW, hy⟩, hQ⟩
    rw [h] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  have h01 : ∀ P ∈ lev Φ A m0 W 0 ⊓ Eig (la m0 0) (lb m0 0),
      D 0 1 P ∈ lev Φ A m0 W 0 ⊓ Eig (la m0 0) (lb m0 0) := by
    rintro P ⟨⟨x, hxW, hx⟩, hP⟩
    exact ⟨⟨_, hW _ _ hxW, isRealized_k01 S.hΦ hx⟩, D_mem hP 0 1⟩
  have h10 : ∀ P ∈ lev Φ A m0 W 0 ⊓ Eig (la m0 0) (lb m0 0),
      D 1 0 P ∈ lev Φ A m0 W 0 ⊓ Eig (la m0 0) (lb m0 0) := by
    rintro P ⟨⟨x, hxW, hx⟩, hP⟩
    exact ⟨⟨_, hW _ _ hxW, isRealized_k10 S.hΦ hx⟩, D_mem hP 1 0⟩
  have hle : lev Φ A m0 W 0 ⊓ Eig (la m0 0) (lb m0 0) ≤ Eig (la m0 0) (lb m0 0) := inf_le_right
  rcases le_or_gt 0 m0 with hm | hm
  · have heig : Eig (la m0 0 : ℂ) (lb m0 0 : ℂ) = Eig (m0.toNat : ℂ) 0 := by
      have : (-m0).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      simp [la, lb, this]
    rw [heig] at hle hV0 h01 h10 ⊢
    exact (Eig_le_of_stable_left m0.toNat _ hle hV0 h01 h10).trans inf_le_left
  · have heig : Eig (la m0 0 : ℂ) (lb m0 0 : ℂ) = Eig 0 ((-m0).toNat : ℂ) := by
      have : m0.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      simp [la, lb, this]
    rw [heig] at hle hV0 h01 h10 ⊢
    exact (Eig_le_of_stable_right (-m0).toNat _ hle hV0 h01 h10).trans inf_le_left

theorem ls_eq_succ_add_one (j : ℕ) : ls A m0 j = ls A m0 (j + 1) + 1 := by
  rw [ls_succ]; ring

include S hW in
/-- **Generation.** If `W` contains all of level `0`, it contains every level. -/
theorem generation (h0 : Eig (la m0 0) (lb m0 0) ≤ lev Φ A m0 W 0) (j : ℕ) :
    Eig (la m0 j) (lb m0 j) ≤ lev Φ A m0 W j := by
  induction j with
  | zero => exact h0
  | succ j ih =>
    intro P' hP'
    rw [la_succ, lb_succ] at hP'
    refine (Submodule.span_le.mpr ?_) (mem_span_zw hP')
    rintro _ ⟨i, k, R, hR, rfl⟩
    obtain ⟨x, hxW, hx⟩ := ih hR
    have hlift : ∀ Q ∈ Eig (la m0 j) (lb m0 j), N * Q ∈ lev Φ A m0 W (j + 1) := by
      intro Q hQ
      obtain ⟨x', hx'W, hx'⟩ := ih hQ
      exact ⟨x', hx'W, (hx'.congr_exp (ls_eq_succ_add_one j)).N_mul⟩
    have hscale : ∀ Q, C (ls A m0 j) * Q ∈ lev Φ A m0 W (j + 1) → Q ∈ lev Φ A m0 W (j + 1) := by
      intro Q h
      have := Submodule.smul_mem _ (ls A m0 j)⁻¹ h
      rwa [smul_eq_C_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (S.hup j), map_one,
        one_mul] at this
    have hanti : ∀ E : Matrix (Fin 2) (Fin 2) ℂ, E.trace = 0 →
        antiT E R ∈ Eig (la m0 j) (lb m0 j) → antiZ E * R ∈ lev Φ A m0 W (j + 1) := by
      intro E hE hT
      apply hscale
      have h1 := isRealized_antihol S.hΦ hx E hE
      have h3 : C (ls A m0 j) * (antiZ E * R) + N * antiT E R ∈ lev Φ A m0 W (j + 1) :=
        ⟨_, hW _ _ hxW, h1.congr_exp (ls_succ A m0 j).symm⟩
      have := sub_mem h3 (hlift _ hT)
      rwa [add_sub_cancel_right] at this
    have hwd : ∀ a b : Fin 2, w a * dw b R ∈ Eig (la m0 j) (lb m0 j) := by
      intro a b
      have := w_mul_mem (dw_mem hR b) a
      rwa [sub_add_cancel] at this
    have h01 : z 1 * (w 0 * R) ∈ lev Φ A m0 W (j + 1) := by
      have := hanti E01 trace_E01 (by rw [antiT_E01]; exact hwd 0 1)
      rw [antiZ_E01] at this
      rwa [← mul_assoc]
    have h10 : z 0 * (w 1 * R) ∈ lev Φ A m0 W (j + 1) := by
      have := hanti E10 trace_E10 (by rw [antiT_E10]; exact hwd 1 0)
      rw [antiZ_E10] at this
      rwa [← mul_assoc]
    have hd : (z 0 * w 0 - z 1 * w 1) * R ∈ lev Φ A m0 W (j + 1) := by
      have := hanti Ed trace_Ed (by rw [antiT_Ed]; exact sub_mem (hwd 0 0) (hwd 1 1))
      rwa [antiZ_Ed] at this
    have hN : N * R ∈ lev Φ A m0 W (j + 1) := hlift R hR
    have h00 : z 0 * (w 0 * R) ∈ lev Φ A m0 W (j + 1) := by
      have := Submodule.smul_mem _ (1 / 2 : ℂ) (add_mem hd hN)
      convert this using 1
      rw [smul_eq_C_mul, N]
      have h2 : (C (1 / 2 : ℂ) : Pol) * 2 = 1 := by
        rw [← map_ofNat C 2, ← map_mul]; norm_num
      linear_combination (-(z 0 * w 0 * R)) * h2
    have h11 : z 1 * (w 1 * R) ∈ lev Φ A m0 W (j + 1) := by
      have := Submodule.smul_mem _ (1 / 2 : ℂ) (sub_mem hN hd)
      convert this using 1
      rw [smul_eq_C_mul, N]
      have h2 : (C (1 / 2 : ℂ) : Pol) * 2 = 1 := by
        rw [← map_ofNat C 2, ← map_mul]; norm_num
      linear_combination (-(z 1 * w 1 * R)) * h2
    fin_cases i <;> fin_cases k
    · exact h00
    · exact h01
    · exact h10
    · exact h11

end Descent

/-- **Algebraic irreducibility.** Under `Setup`, a nonzero subspace stable under
`complexStandardLie 2 ds` is everything. -/
theorem Setup.eq_top (S : Setup ds Φ A m0) (W : Submodule ℂ (KF2 ds))
    (hW : ∀ (Y : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ), ∀ x ∈ W, complexStandardLie 2 ds Y x ∈ W)
    (hne : W ≠ ⊥) : W = ⊤ := by
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨J, P, hP, hx⟩ := S.hF1 x
  obtain ⟨y, hyW, hy0, Q, hQ, hy⟩ := descent S hW J hxW hx0 hP hx
  have hgen := generation S hW (bottom S hW hyW hy0 hQ hy)
  rw [eq_top_iff]
  intro x' _
  obtain ⟨J', P', hP', hx'⟩ := S.hF1 x'
  obtain ⟨x'', hx''W, hx''⟩ := hgen J' hP'
  have : x'' = x' := Subtype.ext (hx''.unique hx')
  rwa [← this]

/-- **Irreducibility from `Setup`.** -/
theorem Setup.isIrreducible (S : Setup ds Φ A m0) (hnt : Nontrivial (KF2 ds)) :
    IsIrreducibleGKModule (complexStandardRep 2 ds) (complexStandardLie 2 ds) := by
  refine ⟨hnt, fun W _ hWL => ?_⟩
  by_cases h : W = ⊥
  · exact Or.inl h
  · exact Or.inr (S.eq_top W hWL h)

end Langlands.Archimedean.GLTwoCore
