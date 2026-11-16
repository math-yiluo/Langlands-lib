import Langlands.GroupScheme.Reductive.LocalSplitTypeA2
import Langlands.GroupScheme.Reductive.LocalSplitConeCommutator

/-! # The commutators of two simple root groups of type `G₂` -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.LinearAlgebra

section RankTwoG2

variable {I : Type*} {J : Type*} [Finite J] [DecidableEq J] {P : RootDatum J (I → ℤ) (I → ℤ)}
  [P.IsReduced] {b : P.Base} {a c : J}

/-- **Roots of type `G₂`, nonnegative coefficients.** If `a`, `c` are distinct simple roots
with `⟨a, c^∨⟩ = -1` and `⟨c, a^∨⟩ = -3` (so `a` is short), the roots `p • a + q • c` with
`p, q ≥ 0` are `a`, `c`, `a + c`, `2 a + c`, `3 a + c` and `3 a + 2 c`. -/
theorem g2_coeffs_of_nonneg (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -3) :
    ∀ (n : ℕ) {α : J} {p q : ℤ}, p + q = n → 0 ≤ p → 0 ≤ q →
      P.root α = p • P.root a + q • P.root c →
      (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 1) ∨ (p = 2 ∧ q = 1) ∨
        (p = 3 ∧ q = 1) ∨ (p = 3 ∧ q = 2) := by
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hli' : LinearIndependent ℤ ![P.root c, P.root a] :=
    b.linearIndependent_pair_of_ne (i := ⟨c, hc⟩) (j := ⟨a, ha⟩)
      (fun h' => hac (congrArg Subtype.val h').symm)
  have eac : (P.chainTopCoeff a c : ℤ) = -P.pairingIn ℤ c a :=
    RootPairing.Base.chainTopCoeff_eq_of_ne (b := b) (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have eca : (P.chainTopCoeff c a : ℤ) = -P.pairingIn ℤ a c :=
    RootPairing.Base.chainTopCoeff_eq_of_ne (b := b) (i := ⟨c, hc⟩) (j := ⟨a, ha⟩)
      (fun h' => hac (congrArg Subtype.val h').symm)
  rw [h2] at eac
  rw [h1] at eca
  -- the roots `a + c` and `2 a + c`
  have hpac : P.pairing a c = -1 := by
    rw [← P.algebraMap_pairingIn ℤ, h1]
    simp
  have hpca : P.pairing c a = -3 := by
    rw [← P.algebraMap_pairingIn ℤ, h2]
    simp
  have hs₁ : P.root (P.reflectionPerm c a) = P.root a + P.root c := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hpac]
    module
  have hp₁a : P.pairing (P.reflectionPerm c a) a = -1 := by
    rw [← RootPairing.root_coroot_eq_pairing, hs₁, map_add, LinearMap.add_apply,
      RootPairing.root_coroot_eq_pairing, RootPairing.root_coroot_eq_pairing,
      RootPairing.pairing_same, hpca]
    norm_num
  have hs₂ : P.root (P.reflectionPerm a (P.reflectionPerm c a)) =
      (2 : ℤ) • P.root a + P.root c := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hp₁a, hs₁]
    module
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α p q hn hp hq h
    by_cases hn2 : n ≤ 2
    · interval_cases n
      · exfalso
        have hp0 : p = 0 := by omega
        have hq0 : q = 0 := by omega
        exact P.ne_zero α (by rw [h, hp0, hq0]; simp)
      · omega
      · rcases (show (p = 2 ∧ q = 0) ∨ (p = 0 ∧ q = 2) ∨ (p = 1 ∧ q = 1) by omega) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hpq
        · exfalso
          exact P.nsmul_notMem_range_root (n := 2) (i := a)
            ⟨α, by rw [h]; simp [two_smul]⟩
        · exfalso
          exact P.nsmul_notMem_range_root (n := 2) (i := c)
            ⟨α, by rw [h]; simp [two_smul]⟩
        · exact Or.inr (Or.inr (Or.inl hpq))
    · obtain ⟨α', hα'⟩ := exists_pred_of_root_eq_pair ha hc hac hp hq (by omega) h
      rcases hα' with ⟨hp1, h'⟩ | ⟨hq1, h'⟩
      · have := ih (n - 1) (by omega) (p := p - 1) (q := q) (by omega) (by omega) hq h'
        rcases (show (p = 2 ∧ q = 1) ∨ (p = 3 ∧ q = 1) ∨ (p = 4 ∧ q = 1) ∨ (p = 4 ∧ q = 2) by
          omega) with hpq | hpq | hpq | hpq
        · exact Or.inr (Or.inr (Or.inr (Or.inl hpq)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpq))))
        · exfalso
          have hmem : P.root c + (4 : ℕ) • P.root a ∈ Set.range P.root :=
            ⟨α, by rw [h, hpq.1, hpq.2]; module⟩
          rw [RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli] at hmem
          omega
        · exfalso
          exact P.nsmul_notMem_range_root (n := 2) (i := P.reflectionPerm a (P.reflectionPerm c a))
            ⟨α, by rw [h, hpq.1, hpq.2, hs₂]; module⟩
      · have := ih (n - 1) (by omega) (p := p) (q := q - 1) (by omega) hp (by omega) h'
        rcases (show (p = 1 ∧ q = 2) ∨ (p = 2 ∧ q = 2) ∨ (p = 3 ∧ q = 2) ∨ (p = 3 ∧ q = 3) by
          omega) with hpq | hpq | hpq | hpq
        · exfalso
          have hmem : P.root a + (2 : ℕ) • P.root c ∈ Set.range P.root :=
            ⟨α, by rw [h, hpq.1, hpq.2]; module⟩
          rw [RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli'] at hmem
          omega
        · exfalso
          exact P.nsmul_notMem_range_root (n := 2) (i := P.reflectionPerm c a)
            ⟨α, by rw [h, hpq.1, hpq.2, hs₁]; module⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpq))))
        · exfalso
          exact P.nsmul_notMem_range_root (n := 3) (i := P.reflectionPerm c a)
            ⟨α, by rw [h, hpq.1, hpq.2, hs₁]; module⟩

/-- **Roots of type `G₂`, all signs.** -/
theorem g2_coeffs (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -3) {α : J} {p q : ℤ}
    (h : P.root α = p • P.root a + q • P.root c) :
    ((p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 1) ∨ (p = 2 ∧ q = 1) ∨
        (p = 3 ∧ q = 1) ∨ (p = 3 ∧ q = 2)) ∨
      ((p = -1 ∧ q = 0) ∨ (p = 0 ∧ q = -1) ∨ (p = -1 ∧ q = -1) ∨ (p = -2 ∧ q = -1) ∨
        (p = -3 ∧ q = -1) ∨ (p = -3 ∧ q = -2)) := by
  rcases sign_of_root_eq_pair ha hc hac h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact Or.inl (g2_coeffs_of_nonneg ha hc hac h1 h2 (p + q).toNat (by omega) hp hq h)
  · have h' : P.root (P.reflectionPerm α α) = (-p) • P.root a + (-q) • P.root c := by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, h]
      simp only [neg_smul, neg_add]
    right
    rcases g2_coeffs_of_nonneg ha hc hac h1 h2 (-p + -q).toNat (by omega) (by omega)
      (by omega) h' with h'' | h'' | h'' | h'' | h'' | h'' <;> omega

end RankTwoG2

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

namespace LocalSplitCell

section TypeG2Group

variable {Γ M : Type*} [CommRing Γ] [Group M]

/-- In a group, an additive map from a ring sends negation to inversion. -/
theorem map_neg_of_add (X : Γ → M) (hX : ∀ s t, X (s + t) = X s * X t) (s : Γ) :
    X (-s) = (X s)⁻¹ := by
  have h0 : X 0 = 1 := by
    have h := hX 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  exact eq_inv_of_mul_eq_one_left (by rw [← hX, neg_add_cancel, h0])

/-- **`G₂`, the conjugation of `Pa` by `Nb`** (SGA 3, Exp. XXIII, 3.4.5). -/
theorem g2_identity_I (Pa Pb P1 P2 P3 P4 Pnb : Γ → M)
    (hP2 : ∀ s t, P2 (s + t) = P2 s * P2 t) (hP3 : ∀ s t, P3 (s + t) = P3 s * P3 t)
    (hP4 : ∀ s t, P4 (s + t) = P4 s * P4 t) (hPnb : ∀ s t, Pnb (s + t) = Pnb s * Pnb t)
    (Nb : M) (hNb : Nb = Pnb (-1) * Pb 1 * Pnb (-1)) (A B C D E F G J : Γ)
    (h1 : ∀ x y, Pb y * Pa x =
      Pa x * Pb y * P1 (A * x * y) * P2 (B * x ^ 2 * y) * P3 (C * x ^ 3 * y) *
        P4 (D * x ^ 3 * y ^ 2))
    (h2 : ∀ x y, P1 y * Pa x =
      Pa x * P1 y * P2 (E * x * y) * P3 (F * x ^ 2 * y) * P4 (G * x * y ^ 2))
    (h4 : ∀ x y, P3 y * Pb x = Pb x * P3 y * P4 (J * x * y))
    (cbb : ∀ y, Nb * Pb y * Nb⁻¹ = Pnb (-y)) (cba : ∀ x, Nb * Pa x * Nb⁻¹ = P1 x)
    (cb1 : ∀ t, Nb * P1 t * Nb⁻¹ = Pa (-t)) (cb2 : ∀ t, Nb * P2 t * Nb⁻¹ = P2 t)
    (cb3 : ∀ t, Nb * P3 t * Nb⁻¹ = P4 t) (cb4 : ∀ t, Nb * P4 t * Nb⁻¹ = P3 (-t))
    (hnba : ∀ x y, Pnb x * Pa y = Pa y * Pnb x) (hb1 : ∀ x y, Pb x * P1 y = P1 y * Pb x)
    (hb2 : ∀ x y, Pb x * P2 y = P2 y * Pb x) (hb4 : ∀ x y, Pb x * P4 y = P4 y * Pb x)
    (hnb2 : ∀ x y, Pnb x * P2 y = P2 y * Pnb x) (hnb3 : ∀ x y, Pnb x * P3 y = P3 y * Pnb x)
    (h23 : ∀ x y, P2 x * P3 y = P3 y * P2 x) (h24 : ∀ x y, P2 x * P4 y = P4 y * P2 x)
    (h34 : ∀ x y, P3 x * P4 y = P4 y * P3 x) :
    Pa 1 * P1 A * P2 B * P3 C * P4 (D - C * J) =
      Pa A * P1 1 * P2 (E * A - B) * P3 (F * A ^ 2 + C * J - D) * P4 (G * A - C) := by
  have conj_mul : ∀ (N x y : M), N * (x * y) * N⁻¹ = (N * x * N⁻¹) * (N * y * N⁻¹) := by
    intro N x y
    group
  have hnbi : (Pnb (-1))⁻¹ = Pnb 1 := by
    rw [← map_neg_of_add Pnb hPnb, neg_neg]
  -- `Nb Pa(1) Nb⁻¹ = P1 1`, expanded
  have hc : Pnb (-1) * Pa 1 * (Pnb (-1))⁻¹ = Pa 1 := by
    rw [hnba]
    group
  have key : P1 1 = Pnb (-1) * (Pb 1 * (Pnb (-1) * Pa 1 * (Pnb (-1))⁻¹) * (Pb 1)⁻¹) *
      (Pnb (-1))⁻¹ := by
    rw [← cba 1, hNb]
    group
  rw [hc] at key
  have S1' : Pb 1 * Pa 1 * (Pb 1)⁻¹ = (Pnb (-1))⁻¹ * P1 1 * Pnb (-1) := by
    rw [key]
    group
  have S1 : Pb 1 * Pa 1 * (Pb 1)⁻¹ = Pnb 1 * P1 1 * (Pnb 1)⁻¹ := by
    rw [S1', hnbi, show Pnb (-1) = (Pnb 1)⁻¹ by rw [← hnbi, inv_inv]]
  -- the left side
  have h11 := h1 1 1
  simp only [mul_one, one_pow] at h11
  have h4c := h4 1 C
  simp only [mul_one] at h4c
  have hbc : Pb 1 * P3 C = P3 C * Pb 1 * (P4 (J * C))⁻¹ := by
    rw [h4c]
    group
  have S2 : Pb 1 * Pa 1 * (Pb 1)⁻¹ = Pa 1 * P1 A * P2 B * P3 C * P4 (D - C * J) := by
    rw [h11]
    calc Pa 1 * Pb 1 * P1 A * P2 B * P3 C * P4 D * (Pb 1)⁻¹
        = Pa 1 * (Pb 1 * P1 A) * P2 B * P3 C * P4 D * (Pb 1)⁻¹ := by group
      _ = Pa 1 * (P1 A * Pb 1) * P2 B * P3 C * P4 D * (Pb 1)⁻¹ := by rw [hb1]
      _ = Pa 1 * P1 A * (Pb 1 * P2 B) * P3 C * P4 D * (Pb 1)⁻¹ := by group
      _ = Pa 1 * P1 A * (P2 B * Pb 1) * P3 C * P4 D * (Pb 1)⁻¹ := by rw [hb2]
      _ = Pa 1 * P1 A * P2 B * (Pb 1 * P3 C) * P4 D * (Pb 1)⁻¹ := by group
      _ = Pa 1 * P1 A * P2 B * (P3 C * Pb 1 * (P4 (J * C))⁻¹) * P4 D * (Pb 1)⁻¹ := by
          rw [hbc]
      _ = Pa 1 * P1 A * P2 B * P3 C * (Pb 1 * ((P4 (J * C))⁻¹ * P4 D)) * (Pb 1)⁻¹ := by
          group
      _ = Pa 1 * P1 A * P2 B * P3 C * (Pb 1 * P4 (D - C * J)) * (Pb 1)⁻¹ := by
          rw [← map_neg_of_add P4 hP4, ← hP4]
          ring_nf
      _ = Pa 1 * P1 A * P2 B * P3 C * (P4 (D - C * J) * Pb 1) * (Pb 1)⁻¹ := by rw [hb4]
      _ = Pa 1 * P1 A * P2 B * P3 C * P4 (D - C * J) := by group
  -- the right side, by the conjugate of `(1)` by `Nb`
  have h5 := congrArg (fun z => Nb * z * Nb⁻¹) (h1 1 (-1))
  simp only [conj_mul, cbb, cba, cb1, cb2, cb3, cb4, mul_one, one_pow, mul_neg, neg_neg,
    neg_one_sq] at h5
  have h7 := congrArg (fun z => Nb * z * Nb⁻¹) (h4 (-1) (-C))
  simp only [conj_mul, cbb, cb3, cb4, mul_neg, neg_neg, mul_one] at h7
  have hnbc : Pnb 1 * P4 (-C) = P4 (-C) * Pnb 1 * P3 (J * C) := by
    have e : P3 (J * C) = (P3 (-J * C))⁻¹ := by
      rw [← map_neg_of_add P3 hP3]
      ring_nf
    rw [e]
    calc Pnb 1 * P4 (-C) = (Pnb 1 * P4 (-C) * P3 (-J * C)) * (P3 (-J * C))⁻¹ := by group
      _ = (P4 (-C) * Pnb 1) * (P3 (-J * C))⁻¹ := by rw [← h7]
  have S3 : Pnb 1 * P1 1 * (Pnb 1)⁻¹ = P1 1 * Pa A * P2 (-B) * P4 (-C) * P3 (C * J - D) := by
    rw [h5]
    calc P1 1 * Pnb 1 * Pa A * P2 (-B) * P4 (-C) * P3 (-D) * (Pnb 1)⁻¹
        = P1 1 * (Pnb 1 * Pa A) * P2 (-B) * P4 (-C) * P3 (-D) * (Pnb 1)⁻¹ := by group
      _ = P1 1 * (Pa A * Pnb 1) * P2 (-B) * P4 (-C) * P3 (-D) * (Pnb 1)⁻¹ := by rw [hnba]
      _ = P1 1 * Pa A * (Pnb 1 * P2 (-B)) * P4 (-C) * P3 (-D) * (Pnb 1)⁻¹ := by group
      _ = P1 1 * Pa A * (P2 (-B) * Pnb 1) * P4 (-C) * P3 (-D) * (Pnb 1)⁻¹ := by rw [hnb2]
      _ = P1 1 * Pa A * P2 (-B) * (Pnb 1 * P4 (-C)) * P3 (-D) * (Pnb 1)⁻¹ := by group
      _ = P1 1 * Pa A * P2 (-B) * (P4 (-C) * Pnb 1 * P3 (J * C)) * P3 (-D) * (Pnb 1)⁻¹ := by
          rw [hnbc]
      _ = P1 1 * Pa A * P2 (-B) * P4 (-C) * (Pnb 1 * (P3 (J * C) * P3 (-D))) * (Pnb 1)⁻¹ := by
          group
      _ = P1 1 * Pa A * P2 (-B) * P4 (-C) * (Pnb 1 * P3 (C * J - D)) * (Pnb 1)⁻¹ := by
          rw [← hP3]
          ring_nf
      _ = P1 1 * Pa A * P2 (-B) * P4 (-C) * (P3 (C * J - D) * Pnb 1) * (Pnb 1)⁻¹ := by
          rw [hnb3]
      _ = P1 1 * Pa A * P2 (-B) * P4 (-C) * P3 (C * J - D) := by group
  -- reorder with `(2)`
  have h2A := h2 A 1
  simp only [mul_one, one_pow] at h2A
  rw [← S2, S1, S3, h2A]
  calc Pa A * P1 1 * P2 (E * A) * P3 (F * A ^ 2) * P4 (G * A) * P2 (-B) * P4 (-C) *
        P3 (C * J - D)
      = Pa A * P1 1 * P2 (E * A) * P3 (F * A ^ 2) * (P4 (G * A) * P2 (-B)) * P4 (-C) *
        P3 (C * J - D) := by group
    _ = Pa A * P1 1 * P2 (E * A) * P3 (F * A ^ 2) * (P2 (-B) * P4 (G * A)) * P4 (-C) *
        P3 (C * J - D) := by rw [← h24]
    _ = Pa A * P1 1 * P2 (E * A) * (P3 (F * A ^ 2) * P2 (-B)) * P4 (G * A) * P4 (-C) *
        P3 (C * J - D) := by group
    _ = Pa A * P1 1 * P2 (E * A) * (P2 (-B) * P3 (F * A ^ 2)) * P4 (G * A) * P4 (-C) *
        P3 (C * J - D) := by rw [← h23]
    _ = Pa A * P1 1 * (P2 (E * A) * P2 (-B)) * P3 (F * A ^ 2) * (P4 (G * A) * P4 (-C)) *
        P3 (C * J - D) := by group
    _ = Pa A * P1 1 * P2 (E * A - B) * P3 (F * A ^ 2) * P4 (G * A - C) *
        P3 (C * J - D) := by rw [← hP2, ← hP4]; ring_nf
    _ = Pa A * P1 1 * P2 (E * A - B) * P3 (F * A ^ 2) * (P4 (G * A - C) *
        P3 (C * J - D)) := by group
    _ = Pa A * P1 1 * P2 (E * A - B) * P3 (F * A ^ 2) * (P3 (C * J - D) *
        P4 (G * A - C)) := by rw [← h34]
    _ = Pa A * P1 1 * P2 (E * A - B) * (P3 (F * A ^ 2) * P3 (C * J - D)) *
        P4 (G * A - C) := by group
    _ = Pa A * P1 1 * P2 (E * A - B) * P3 (F * A ^ 2 + C * J - D) * P4 (G * A - C) := by
        rw [← hP3]; ring_nf

/-- **`G₂`, the conjugation of `Pb` by `Na`** (SGA 3, Exp. XXIII, 3.4.6). -/
theorem g2_identity_II (Pa Pb P1 P2 P3 P4 Pna : Γ → M)
    (hPa : ∀ s t, Pa (s + t) = Pa s * Pa t) (hP4 : ∀ s t, P4 (s + t) = P4 s * P4 t)
    (hPna : ∀ s t, Pna (s + t) = Pna s * Pna t)
    (Na : M) (hNa : Na = Pna (-1) * Pa 1 * Pna (-1)) (A B C D H J : Γ)
    (h1 : ∀ x y, Pb y * Pa x =
      Pa x * Pb y * P1 (A * x * y) * P2 (B * x ^ 2 * y) * P3 (C * x ^ 3 * y) *
        P4 (D * x ^ 3 * y ^ 2))
    (h4 : ∀ x y, P3 y * Pb x = Pb x * P3 y * P4 (J * x * y))
    (h6 : ∀ x y, P2 y * P1 x = P1 x * P2 y * P4 (H * x * y))
    (caa : ∀ x, Na * Pa x * Na⁻¹ = Pna (-x)) (cab : ∀ y, Na * Pb y * Na⁻¹ = P3 (-y))
    (ca1 : ∀ t, Na * P1 t * Na⁻¹ = P2 t) (ca2 : ∀ t, Na * P2 t * Na⁻¹ = P1 (-t))
    (ca3 : ∀ t, Na * P3 t * Na⁻¹ = Pb t) (ca4 : ∀ t, Na * P4 t * Na⁻¹ = P4 t)
    (hnab : ∀ x y, Pna x * Pb y = Pb y * Pna x) (hb1 : ∀ x y, Pb x * P1 y = P1 y * Pb x)
    (hb2 : ∀ x y, Pb x * P2 y = P2 y * Pb x) (hb4 : ∀ x y, Pb x * P4 y = P4 y * Pb x)
    (h13 : ∀ x y, P1 x * P3 y = P3 y * P1 x) (h14 : ∀ x y, P1 x * P4 y = P4 y * P1 x)
    (h23 : ∀ x y, P2 x * P3 y = P3 y * P2 x) (h24 : ∀ x y, P2 x * P4 y = P4 y * P2 x) :
    Pb 1 * P1 (-A) * P2 B * P3 (-C) * P4 (-D) =
      Pb C * P1 (-B) * P2 A * P3 (-1) * P4 (D - C * J - A * B * H) := by
  have conj_mul : ∀ (N x y : M), N * (x * y) * N⁻¹ = (N * x * N⁻¹) * (N * y * N⁻¹) := by
    intro N x y
    group
  have hnai : (Pna (-1))⁻¹ = Pna 1 := by
    rw [← map_neg_of_add Pna hPna, neg_neg]
  -- `Na Pb(1) Na⁻¹ = P3 (-1)`, expanded
  have hc : Pna (-1) * Pb 1 * (Pna (-1))⁻¹ = Pb 1 := by
    rw [hnab]
    group
  have key : P3 (-1) = Pna (-1) * (Pa 1 * (Pna (-1) * Pb 1 * (Pna (-1))⁻¹) * (Pa 1)⁻¹) *
      (Pna (-1))⁻¹ := by
    rw [← cab 1, hNa]
    group
  rw [hc] at key
  have T1 : Pa 1 * Pb 1 * (Pa 1)⁻¹ = (Pna (-1))⁻¹ * P3 (-1) * Pna (-1) := by
    rw [key]
    group
  -- the left side by `(1)` at `x = -1`
  have e3 : (-1 : Γ) ^ 3 = -1 := by norm_num
  have h1m := h1 (-1) 1
  simp only [mul_one, neg_one_sq, mul_neg, one_pow, e3, mul_one] at h1m
  rw [map_neg_of_add Pa hPa] at h1m
  have T2 : Pa 1 * Pb 1 * (Pa 1)⁻¹ = Pb 1 * P1 (-A) * P2 B * P3 (-C) * P4 (-D) := by
    calc Pa 1 * Pb 1 * (Pa 1)⁻¹ = Pa 1 * (Pb 1 * (Pa 1)⁻¹) := by group
      _ = Pa 1 * ((Pa 1)⁻¹ * Pb 1 * P1 (-A) * P2 B * P3 (-C) * P4 (-D)) := by rw [h1m]
      _ = Pb 1 * P1 (-A) * P2 B * P3 (-C) * P4 (-D) := by group
  -- the right side by `(8)`, the conjugate of `(1)` by `Na`
  have h8 := congrArg (fun z => Na * z * Na⁻¹) (h1 1 1)
  simp only [conj_mul, caa, cab, ca1, ca2, ca3, ca4, mul_one, one_pow] at h8
  have T3 : (Pna (-1))⁻¹ * P3 (-1) * Pna (-1) = P3 (-1) * P2 A * P1 (-B) * Pb C * P4 D := by
    calc (Pna (-1))⁻¹ * P3 (-1) * Pna (-1) = (Pna (-1))⁻¹ * (P3 (-1) * Pna (-1)) := by group
      _ = (Pna (-1))⁻¹ * (Pna (-1) * P3 (-1) * P2 A * P1 (-B) * Pb C * P4 D) := by rw [h8]
      _ = P3 (-1) * P2 A * P1 (-B) * Pb C * P4 D := by group
  -- reorder
  have e6 := h6 (-B) A
  have e4 := h4 C (-1)
  rw [← T2, T1, T3]
  calc P3 (-1) * P2 A * P1 (-B) * Pb C * P4 D
      = P3 (-1) * (P2 A * P1 (-B)) * Pb C * P4 D := by group
    _ = P3 (-1) * (P1 (-B) * P2 A * P4 (H * -B * A)) * Pb C * P4 D := by rw [e6]
    _ = P3 (-1) * P1 (-B) * P2 A * (P4 (H * -B * A) * Pb C) * P4 D := by group
    _ = P3 (-1) * P1 (-B) * P2 A * (Pb C * P4 (H * -B * A)) * P4 D := by rw [hb4]
    _ = P3 (-1) * P1 (-B) * (P2 A * Pb C) * P4 (H * -B * A) * P4 D := by group
    _ = P3 (-1) * P1 (-B) * (Pb C * P2 A) * P4 (H * -B * A) * P4 D := by rw [hb2]
    _ = P3 (-1) * (P1 (-B) * Pb C) * P2 A * P4 (H * -B * A) * P4 D := by group
    _ = P3 (-1) * (Pb C * P1 (-B)) * P2 A * P4 (H * -B * A) * P4 D := by rw [hb1]
    _ = (P3 (-1) * Pb C) * P1 (-B) * P2 A * P4 (H * -B * A) * P4 D := by group
    _ = (Pb C * P3 (-1) * P4 (J * C * -1)) * P1 (-B) * P2 A * P4 (H * -B * A) * P4 D := by
        rw [e4]
    _ = Pb C * P3 (-1) * (P4 (J * C * -1) * P1 (-B)) * P2 A * P4 (H * -B * A) * P4 D := by
        group
    _ = Pb C * P3 (-1) * (P1 (-B) * P4 (J * C * -1)) * P2 A * P4 (H * -B * A) * P4 D := by
        rw [← h14]
    _ = Pb C * (P3 (-1) * P1 (-B)) * P4 (J * C * -1) * P2 A * P4 (H * -B * A) * P4 D := by
        group
    _ = Pb C * (P1 (-B) * P3 (-1)) * P4 (J * C * -1) * P2 A * P4 (H * -B * A) * P4 D := by
        rw [← h13]
    _ = Pb C * P1 (-B) * P3 (-1) * (P4 (J * C * -1) * P2 A) * P4 (H * -B * A) * P4 D := by
        group
    _ = Pb C * P1 (-B) * P3 (-1) * (P2 A * P4 (J * C * -1)) * P4 (H * -B * A) * P4 D := by
        rw [← h24]
    _ = Pb C * P1 (-B) * (P3 (-1) * P2 A) * P4 (J * C * -1) * P4 (H * -B * A) * P4 D := by
        group
    _ = Pb C * P1 (-B) * (P2 A * P3 (-1)) * P4 (J * C * -1) * P4 (H * -B * A) * P4 D := by
        rw [← h23]
    _ = Pb C * P1 (-B) * P2 A * P3 (-1) * (P4 (J * C * -1) * P4 (H * -B * A) * P4 D) := by
        group
    _ = Pb C * P1 (-B) * P2 A * P3 (-1) * P4 (D - C * J - A * B * H) := by
        rw [← hP4, ← hP4]
        ring_nf

/-- **`G₂`, the conjugation of `P3` by `Nb`** (SGA 3, Exp. XXIII, 3.4.7). -/
theorem g2_identity_III (Pb P3 P4 Pnb : Γ → M)
    (hPb : ∀ s t, Pb (s + t) = Pb s * Pb t) (Nb : M) (hNb : Nb = Pnb (-1) * Pb 1 * Pnb (-1)) (J : Γ)
    (h4 : ∀ x y, P3 y * Pb x = Pb x * P3 y * P4 (J * x * y))
    (cbb : ∀ y, Nb * Pb y * Nb⁻¹ = Pnb (-y)) (cb3 : ∀ t, Nb * P3 t * Nb⁻¹ = P4 t)
    (cb4 : ∀ t, Nb * P4 t * Nb⁻¹ = P3 (-t)) (hnb3 : ∀ x y, Pnb x * P3 y = P3 y * Pnb x) :
    P3 1 * P4 (-J) = P4 1 * P3 (-J) := by
  have conj_mul : ∀ (N x y : M), N * (x * y) * N⁻¹ = (N * x * N⁻¹) * (N * y * N⁻¹) := by
    intro N x y
    group
  have hc : Pnb (-1) * P3 1 * (Pnb (-1))⁻¹ = P3 1 := by
    rw [hnb3]
    group
  have key : P4 1 = Pnb (-1) * (Pb 1 * (Pnb (-1) * P3 1 * (Pnb (-1))⁻¹) * (Pb 1)⁻¹) *
      (Pnb (-1))⁻¹ := by
    rw [← cb3 1, hNb]
    group
  rw [hc] at key
  have U1 : Pb 1 * P3 1 * (Pb 1)⁻¹ = (Pnb (-1))⁻¹ * P4 1 * Pnb (-1) := by
    rw [key]
    group
  have h4m := h4 (-1) 1
  simp only [mul_one, mul_neg] at h4m
  rw [map_neg_of_add Pb hPb] at h4m
  have U2 : Pb 1 * P3 1 * (Pb 1)⁻¹ = P3 1 * P4 (-J) := by
    calc Pb 1 * P3 1 * (Pb 1)⁻¹ = Pb 1 * (P3 1 * (Pb 1)⁻¹) := by group
      _ = Pb 1 * ((Pb 1)⁻¹ * P3 1 * P4 (-J)) := by rw [h4m]
      _ = P3 1 * P4 (-J) := by group
  have h7 := congrArg (fun z => Nb * z * Nb⁻¹) (h4 1 1)
  simp only [conj_mul, cbb, cb3, cb4, mul_one] at h7
  have U3 : (Pnb (-1))⁻¹ * P4 1 * Pnb (-1) = P4 1 * P3 (-J) := by
    calc (Pnb (-1))⁻¹ * P4 1 * Pnb (-1) = (Pnb (-1))⁻¹ * (P4 1 * Pnb (-1)) := by group
      _ = (Pnb (-1))⁻¹ * (Pnb (-1) * P4 1 * P3 (-J)) := by rw [h7]
      _ = P4 1 * P3 (-J) := by group
  rw [← U2, U1, U3]

/-- **`G₂`, the conjugation of `P1` by `Na`** (SGA 3, Exp. XXIII, 3.4.8). The coordinate at
`3 a + c` of the right side is `H`; the coordinate at `3 a + 2 c` is some `W`. -/
theorem g2_identity_IV (Pa Pb P1 P2 P3 P4 Pna : Γ → M)
    (hPa : ∀ s t, Pa (s + t) = Pa s * Pa t) (hPb : ∀ s t, Pb (s + t) = Pb s * Pb t)
    (hP1 : ∀ s t, P1 (s + t) = P1 s * P1 t) (hP2 : ∀ s t, P2 (s + t) = P2 s * P2 t)
    (hP4 : ∀ s t, P4 (s + t) = P4 s * P4 t) (hPna : ∀ s t, Pna (s + t) = Pna s * Pna t)
    (Na : M) (hNa : Na = Pna (-1) * Pa 1 * Pna (-1)) (A B C D E F G H J : Γ)
    (h1 : ∀ x y, Pb y * Pa x =
      Pa x * Pb y * P1 (A * x * y) * P2 (B * x ^ 2 * y) * P3 (C * x ^ 3 * y) *
        P4 (D * x ^ 3 * y ^ 2))
    (h2 : ∀ x y, P1 y * Pa x =
      Pa x * P1 y * P2 (E * x * y) * P3 (F * x ^ 2 * y) * P4 (G * x * y ^ 2))
    (h3 : ∀ x y, P2 y * Pa x = Pa x * P2 y * P3 (H * x * y))
    (h4 : ∀ x y, P3 y * Pb x = Pb x * P3 y * P4 (J * x * y))
    (h6 : ∀ x y, P2 y * P1 x = P1 x * P2 y * P4 (H * x * y))
    (caa : ∀ x, Na * Pa x * Na⁻¹ = Pna (-x)) (cana : ∀ x, Na * Pna x * Na⁻¹ = Pa (-x))
    (cab : ∀ y, Na * Pb y * Na⁻¹ = P3 (-y))
    (ca1 : ∀ t, Na * P1 t * Na⁻¹ = P2 t) (ca2 : ∀ t, Na * P2 t * Na⁻¹ = P1 (-t))
    (ca3 : ∀ t, Na * P3 t * Na⁻¹ = Pb t) (ca4 : ∀ t, Na * P4 t * Na⁻¹ = P4 t)
    (hb1 : ∀ x y, Pb x * P1 y = P1 y * Pb x)
    (hb2 : ∀ x y, Pb x * P2 y = P2 y * Pb x) (hb4 : ∀ x y, Pb x * P4 y = P4 y * Pb x)
    (h13 : ∀ x y, P1 x * P3 y = P3 y * P1 x) (h14 : ∀ x y, P1 x * P4 y = P4 y * P1 x)
    (h23 : ∀ x y, P2 x * P3 y = P3 y * P2 x) (h24 : ∀ x y, P2 x * P4 y = P4 y * P2 x)
    (h34 : ∀ x y, P3 x * P4 y = P4 y * P3 x) :
    ∃ W : Γ, P1 1 * P2 (-E) * P3 F * P4 (-G) =
      Pb (F - C * H) * P1 (B * H - E) * P2 (1 - A * H) * P3 H * P4 W := by
  have conj_mul : ∀ (N x y : M), N * (x * y) * N⁻¹ = (N * x * N⁻¹) * (N * y * N⁻¹) := by
    intro N x y
    group
  have hnai : (Pna (-1))⁻¹ = Pna 1 := by
    rw [← map_neg_of_add Pna hPna, neg_neg]
  -- the second form of `Na`
  have hNa' : Na = Pa 1 * Pna (-1) * Pa 1 := by
    have h := congrArg (fun z => Na * z * Na⁻¹) hNa
    simp only [conj_mul, caa, cana, neg_neg] at h
    rw [← h]
    group
  -- `Na P1(1) Na⁻¹ = P2 1`, expanded
  have key : Pa 1 * P1 1 * (Pa 1)⁻¹ = Pna 1 * ((Pa 1)⁻¹ * P2 1 * Pa 1) * (Pna 1)⁻¹ := by
    have h := ca1 1
    rw [hNa'] at h
    rw [← hnai, ← h]
    group
  -- the left side by `(2)` at `x = -1`
  have h2m := h2 (-1) 1
  simp only [mul_one, neg_one_sq, mul_neg, one_pow] at h2m
  rw [map_neg_of_add Pa hPa] at h2m
  have V1 : Pa 1 * P1 1 * (Pa 1)⁻¹ = P1 1 * P2 (-E) * P3 F * P4 (-G) := by
    calc Pa 1 * P1 1 * (Pa 1)⁻¹ = Pa 1 * (P1 1 * (Pa 1)⁻¹) := by group
      _ = Pa 1 * ((Pa 1)⁻¹ * P1 1 * P2 (-E) * P3 F * P4 (-G)) := by rw [h2m]
      _ = P1 1 * P2 (-E) * P3 F * P4 (-G) := by group
  -- the inner conjugate by `(3)`
  have h31 := h3 1 1
  simp only [mul_one] at h31
  have V2 : (Pa 1)⁻¹ * P2 1 * Pa 1 = P2 1 * P3 H := by
    calc (Pa 1)⁻¹ * P2 1 * Pa 1 = (Pa 1)⁻¹ * (P2 1 * Pa 1) := by group
      _ = (Pa 1)⁻¹ * (Pa 1 * P2 1 * P3 H) := by rw [h31]
      _ = P2 1 * P3 H := by group
  -- conjugation of `P2 1` and `P3 H` by `Pna 1`, from the conjugates of `(2)` and `(1)`
  have h9 := congrArg (fun z => Na * z * Na⁻¹) (h2 1 1)
  simp only [conj_mul, caa, ca1, ca2, ca3, ca4, mul_one, one_pow] at h9
  have V3 : Pna 1 * P2 1 * (Pna 1)⁻¹ = P2 1 * P1 (-E) * Pb F * P4 G := by
    rw [← hnai]
    calc (Pna (-1))⁻¹ * P2 1 * (Pna (-1))⁻¹⁻¹ = (Pna (-1))⁻¹ * (P2 1 * Pna (-1)) := by group
      _ = (Pna (-1))⁻¹ * (Pna (-1) * P2 1 * P1 (-E) * Pb F * P4 G) := by rw [h9]
      _ = P2 1 * P1 (-E) * Pb F * P4 G := by group
  have h8 := congrArg (fun z => Na * z * Na⁻¹) (h1 1 (-H))
  simp only [conj_mul, caa, cab, ca1, ca2, ca3, ca4, mul_one, one_pow, neg_neg, mul_neg,
    neg_sq] at h8
  have V4 : Pna 1 * P3 H * (Pna 1)⁻¹ = P3 H * P2 (-(A * H)) * P1 (B * H) * Pb (-(C * H)) *
      P4 (D * H ^ 2) := by
    rw [← hnai]
    calc (Pna (-1))⁻¹ * P3 H * (Pna (-1))⁻¹⁻¹ = (Pna (-1))⁻¹ * (P3 H * Pna (-1)) := by group
      _ = (Pna (-1))⁻¹ * (Pna (-1) * P3 H * P2 (-(A * H)) * P1 (B * H) * Pb (-(C * H)) *
          P4 (D * H ^ 2)) := by rw [h8]
      _ = P3 H * P2 (-(A * H)) * P1 (B * H) * Pb (-(C * H)) * P4 (D * H ^ 2) := by group
  have key2 : P1 1 * P2 (-E) * P3 F * P4 (-G) =
      (P2 1 * P1 (-E) * Pb F * P4 G) *
        (P3 H * P2 (-(A * H)) * P1 (B * H) * Pb (-(C * H)) * P4 (D * H ^ 2)) := by
    rw [← V1, key, V2, ← V3, ← V4]
    group
  -- reordering rules, in right-associated form
  have r_b1 : ∀ x y z, P1 y * (Pb x * z) = Pb x * (P1 y * z) := by
    intro x y z; rw [← mul_assoc (P1 y), ← hb1 x y]; simp only [mul_assoc]
  have r_b2 : ∀ x y z, P2 y * (Pb x * z) = Pb x * (P2 y * z) := by
    intro x y z; rw [← mul_assoc (P2 y), ← hb2 x y]; simp only [mul_assoc]
  have r_b4 : ∀ x y z, P4 y * (Pb x * z) = Pb x * (P4 y * z) := by
    intro x y z; rw [← mul_assoc (P4 y), ← hb4 x y]; simp only [mul_assoc]
  have r_3b : ∀ x y z, P3 y * (Pb x * z) = Pb x * (P3 y * (P4 (J * x * y) * z)) := by
    intro x y z; rw [← mul_assoc (P3 y), h4 x y]; simp only [mul_assoc]
  have r_21 : ∀ x y z, P2 y * (P1 x * z) = P1 x * (P2 y * (P4 (H * x * y) * z)) := by
    intro x y z; rw [← mul_assoc (P2 y), h6 x y]; simp only [mul_assoc]
  have r_31 : ∀ x y z, P3 y * (P1 x * z) = P1 x * (P3 y * z) := by
    intro x y z; rw [← mul_assoc (P3 y), ← h13 x y]; simp only [mul_assoc]
  have r_41 : ∀ x y z, P4 y * (P1 x * z) = P1 x * (P4 y * z) := by
    intro x y z; rw [← mul_assoc (P4 y), ← h14 x y]; simp only [mul_assoc]
  have r_32 : ∀ x y z, P3 y * (P2 x * z) = P2 x * (P3 y * z) := by
    intro x y z; rw [← mul_assoc (P3 y), ← h23 x y]; simp only [mul_assoc]
  have r_42 : ∀ x y z, P4 y * (P2 x * z) = P2 x * (P4 y * z) := by
    intro x y z; rw [← mul_assoc (P4 y), ← h24 x y]; simp only [mul_assoc]
  have r_43 : ∀ x y z, P4 y * (P3 x * z) = P3 x * (P4 y * z) := by
    intro x y z; rw [← mul_assoc (P4 y), ← h34 x y]; simp only [mul_assoc]
  have m_b : ∀ x y z, Pb x * (Pb y * z) = Pb (x + y) * z := by
    intro x y z; rw [← mul_assoc, ← hPb]
  have m_1 : ∀ x y z, P1 x * (P1 y * z) = P1 (x + y) * z := by
    intro x y z; rw [← mul_assoc, ← hP1]
  have m_2 : ∀ x y z, P2 x * (P2 y * z) = P2 (x + y) * z := by
    intro x y z; rw [← mul_assoc, ← hP2]
  have m_4 : ∀ x y z, P4 x * (P4 y * z) = P4 (x + y) * z := by
    intro x y z; rw [← mul_assoc, ← hP4]
  have hcongr : ∀ x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : Γ, x1 = y1 → x2 = y2 → x3 = y3 →
      x4 = y4 → x5 = y5 →
      Pb x1 * (P1 x2 * (P2 x3 * (P3 x4 * (P4 x5 * 1)))) =
        Pb y1 * (P1 y2 * (P2 y3 * (P3 y4 * (P4 y5 * 1)))) := by
    rintro _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl
    rfl
  refine ⟨G + D * H ^ 2 + H * (-E) + H * (B * H) + H * (B * H) * (-(A * H)) +
    J * (-(C * H)) * H, ?_⟩
  rw [key2]
  apply mul_right_cancel (b := (1 : M))
  simp only [mul_assoc, r_b1, r_b2, r_b4, r_3b, r_21, r_31, r_41, r_32, r_42, r_43, m_b, m_1,
    m_2, m_4]
  refine hcongr _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ <;> ring

end TypeG2Group

section TypeG2

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {v : J → (Ga R ⟶ G)}

omit [DecidableEq I] in
/-- **Uniqueness of five coordinates.** Products of root points along five distinct positive
roots of a base determine their coordinates. -/
theorem eq_of_prod_five (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    (b : P.Base) {x₀ x₁ x₂ x₃ x₄ : J} (hL : [x₀, x₁, x₂, x₃, x₄].Nodup)
    (hpos : ∀ x ∈ [x₀, x₁, x₂, x₃, x₄], b.IsPos x)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    {a₀ a₁ a₂ a₃ a₄ c₀ c₁ c₂ c₃ c₄ : Γ((Over.mk s).left, ⊤)}
    (h : rootPoint (v x₀) (Over.mk s) a₀ * rootPoint (v x₁) (Over.mk s) a₁ *
        rootPoint (v x₂) (Over.mk s) a₂ * rootPoint (v x₃) (Over.mk s) a₃ *
        rootPoint (v x₄) (Over.mk s) a₄ =
      rootPoint (v x₀) (Over.mk s) c₀ * rootPoint (v x₁) (Over.mk s) c₁ *
        rootPoint (v x₂) (Over.mk s) c₂ * rootPoint (v x₃) (Over.mk s) c₃ *
        rootPoint (v x₄) (Over.mk s) c₄) :
    a₀ = c₀ ∧ a₁ = c₁ ∧ a₂ = c₂ ∧ a₃ = c₃ ∧ a₄ = c₄ := by
  have e := listProd_rootPoint_injective hG hmax hP hv b [x₀, x₁, x₂, x₃, x₄] hL hpos s
    (x := ![a₀, a₁, a₂, a₃, a₄]) (y := ![c₀, c₁, c₂, c₃, c₄]) (by
      simp only [List.length_cons, List.length_nil, List.ofFn_succ, List.ofFn_zero,
        List.prod_cons, List.prod_nil, mul_one]
      simpa [mul_assoc] using h)
  exact ⟨congrFun e 0, congrFun e 1, congrFun e 2, congrFun e 3, congrFun e 4⟩

omit [DecidableEq I] in
/-- **Uniqueness of two coordinates.** -/
theorem eq_of_prod_two (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    (b : P.Base) {x₀ x₁ : J} (hL : [x₀, x₁].Nodup) (hpos : ∀ x ∈ [x₀, x₁], b.IsPos x)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    {a₀ a₁ c₀ c₁ : Γ((Over.mk s).left, ⊤)}
    (h : rootPoint (v x₀) (Over.mk s) a₀ * rootPoint (v x₁) (Over.mk s) a₁ =
      rootPoint (v x₀) (Over.mk s) c₀ * rootPoint (v x₁) (Over.mk s) c₁) :
    a₀ = c₀ ∧ a₁ = c₁ := by
  have e := listProd_rootPoint_injective hG hmax hP hv b [x₀, x₁] hL hpos s
    (x := ![a₀, a₁]) (y := ![c₀, c₁]) (by
      simp only [List.length_cons, List.length_nil, List.ofFn_succ, List.ofFn_zero,
        List.prod_cons, List.prod_nil, mul_one]
      simpa [mul_assoc] using h)
  exact ⟨congrFun e 0, congrFun e 1⟩

set_option maxHeartbeats 1000000 in
/-- **The `G₂` commutator constants.** Let `a` (short) and `c` (long) be simple roots of a base
with `⟨a, c^∨⟩ = -1` and `⟨c, a^∨⟩ = -3`, and let `v` be root parametrizations of all roots
whose points `N_a = v_{-a}(-1) v_a(1) v_{-a}(-1)` and `N_c` are Weyl points acting by `s_a`
and `s_c`. Assume the rank-one identities `N_a v_a(x) N_a⁻¹ = v_{-a}(-x)`,
`N_c v_c(x) N_c⁻¹ = v_{-c}(-x)`, and that `N_a²` and `N_c²` act on every root parametrization
`w` of a root `β` by the signs `(-1)^⟨β, a^∨⟩` and `(-1)^⟨β, c^∨⟩`. Put `p₁ = Ad(N_c) ∘ v_a`
(root `a + c`), `p₂ = Ad(N_a) ∘ p₁` (root `2 a + c`), `p₃ = Ad(N_a) ∘ v_c` (root `3 a + c`) and
`p₄ = Ad(N_c) ∘ p₃` (root `3 a + 2 c`). Then over every ring over `R`, with
`[g, h] = (g h)⁻¹ (h g)`:
`[v_a(x), v_c(y)] = p₁(x y) p₂(x² y) p₃(-x³ y) p₄(-x³ y²)`,
`[v_a(x), p₁(y)] = p₂(2 x y) p₃(-3 x² y) p₄(-3 x y²)`, `[v_a(x), p₂(y)] = p₃(-3 x y)`,
`[v_c(x), p₃(y)] = p₄(-x y)` and `[p₁(x), p₂(y)] = p₄(-3 x y)`. -/
theorem g2_constants (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    {b : P.Base} {a c : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -3)
    (hna : IsWeylPoint i (weylPoint (v a) (v (P.reflectionPerm a a))) (P.reflection a))
    (hnc : IsWeylPoint i (weylPoint (v c) (v (P.reflectionPerm c c))) (P.reflection c))
    (hROa : (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)),
      G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
          rootPoint (v a) (Over.mk s) x *
          (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s))⁻¹ =
        rootPoint (v (P.reflectionPerm a a)) (Over.mk s) (-x)))
    (hROc : (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)),
      G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s) *
          rootPoint (v c) (Over.mk s) x *
          (G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s))⁻¹ =
        rootPoint (v (P.reflectionPerm c c)) (Over.mk s) (-x)))
    (hsqa : (∀ (β : J) (w : Ga R ⟶ G), IsRootParametrization i (P.root β) w →
      ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)),
      (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
          G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s)) *
          rootPoint w (Over.mk s) x *
          (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
            G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s))⁻¹ =
        rootPoint w (Over.mk s) ((P.pairingIn ℤ β a).negOnePow • x)))
    (hsqc : (∀ (β : J) (w : Ga R ⟶ G), IsRootParametrization i (P.root β) w →
      ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)),
      (G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s) *
          G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s)) *
          rootPoint w (Over.mk s) x *
          (G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s) *
            G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s))⁻¹ =
        rootPoint w (Over.mk s) ((P.pairingIn ℤ β c).negOnePow • x))) :
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (x * y)) *
        rootPoint ((v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) ≫
            (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (x ^ 2 * y)) *
        rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(x ^ 3 * y))) *
        rootPoint ((v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) ≫
            (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(x ^ 3 * y ^ 2)))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk
              s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk
            s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint ((v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) ≫
          (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (2 * x * y)) *
        rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(3 * x ^ 2 * y))) *
        rootPoint ((v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) ≫
            (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(3 * x * y ^ 2)))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint ((v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) ≫
              (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
              ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint ((v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) ≫
            (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(3 * x * y)))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk
              s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk
            s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint ((v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) ≫
          (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(x * y)))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint ((v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) ≫
              (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
              ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint ((v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) ≫
            (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk
              s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint ((v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) ≫
          (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(3 * x * y)))) := by
  classical
  have := hP.finite
  have : P.IsReduced := hP.isReduced
  set na := P.reflectionPerm a a with hna_def
  set nc := P.reflectionPerm c c with hnc_def
  set Na := weylPoint (v a) (v na) with hNa_def
  set Nc := weylPoint (v c) (v nc) with hNc_def
  set p₁ := v a ≫ (G.innerIso Nc).hom with hp₁_def
  set p₂ := p₁ ≫ (G.innerIso Na).hom with hp₂_def
  set p₃ := v c ≫ (G.innerIso Na).hom with hp₃_def
  set p₄ := p₃ ≫ (G.innerIso Nc).hom with hp₄_def
  set d₁ := P.reflectionPerm c a with hd₁_def
  set d₂ := P.reflectionPerm a d₁ with hd₂_def
  set d₃ := P.reflectionPerm a c with hd₃_def
  set d₄ := P.reflectionPerm c d₃ with hd₄_def
  have hpI : ∀ x y : J, P.pairingIn ℤ x y = P.pairing x y := by
    intro x y
    rw [← P.algebraMap_pairingIn ℤ]
    simp
  have hpac : P.pairing a c = -1 := by rw [← hpI, h1]
  have hpca : P.pairing c a = -3 := by rw [← hpI, h2]
  have hpair : ∀ {α : J} {p q : ℤ}, P.root α = p • P.root a + q • P.root c → ∀ x : J,
      P.pairing α x = p * P.pairing a x + q * P.pairing c x := by
    intro α p q h x
    rw [← RootPairing.root_coroot_eq_pairing, h]
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply,
      RootPairing.root_coroot_eq_pairing, smul_eq_mul]
  -- the roots involved, as combinations of `a` and `c`
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  have rc : P.root c = (0 : ℤ) • P.root a + (1 : ℤ) • P.root c := by simp
  have rna : P.root na = (-1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by
    rw [hna_def, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    simp
  have rnc : P.root nc = (0 : ℤ) • P.root a + (-1 : ℤ) • P.root c := by
    rw [hnc_def, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    simp
  have rd₁ : P.root d₁ = (1 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [hd₁_def, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hpac]
    module
  have hpd₁a : P.pairing d₁ a = -1 := by
    rw [hpair rd₁, RootPairing.pairing_same, hpca]
    norm_num
  have rd₂ : P.root d₂ = (2 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [hd₂_def, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hpd₁a, rd₁]
    module
  have rd₃ : P.root d₃ = (3 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [hd₃_def, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hpca]
    module
  have hpd₃c : P.pairing d₃ c = -1 := by
    rw [hpair rd₃, RootPairing.pairing_same, hpac]
    norm_num
  have rd₄ : P.root d₄ = (3 : ℤ) • P.root a + (2 : ℤ) • P.root c := by
    rw [hd₄_def, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hpd₃c, rd₃]
    module
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hdist : ∀ {x y : J} {p q p' q' : ℤ}, P.root x = p • P.root a + q • P.root c →
      P.root y = p' • P.root a + q' • P.root c → (p ≠ p' ∨ q ≠ q') → x ≠ y := by
    intro x y p q p' q' hx hy hpq hxy
    subst hxy
    have h0 : (p - p') • P.root a + (q - q') • P.root c = 0 := by
      rw [sub_smul, sub_smul]
      have := hx.symm.trans hy
      rw [← sub_eq_zero] at this
      rw [← this]
      abel
    have := LinearIndependent.pair_iff.mp hli _ _ h0
    omega
  have hsame : ∀ {x y : J} {p q : ℤ}, P.root x = p • P.root a + q • P.root c →
      P.root y = p • P.root a + q • P.root c → x = y :=
    fun hx hy => P.root.injective (hx.trans hy.symm)
  have hcoeff := fun {α : J} {p q : ℤ} (h : P.root α = p • P.root a + q • P.root c) =>
    Langlands.LinearAlgebra.g2_coeffs ha hc hac h1 h2 h
  have cone_gen : ∀ {x y : J} {p q p' q' : ℤ}, P.root x = p • P.root a + q • P.root c →
      P.root y = p' • P.root a + q' • P.root c → ∀ (α : J) (dS dT : ℕ),
      (dS : ℤ) • P.root x + (dT : ℤ) • P.root y = P.root α →
      let P' := (dS : ℤ) * p + (dT : ℤ) * p'
      let Q' := (dS : ℤ) * q + (dT : ℤ) * q'
      ((P' = 1 ∧ Q' = 0) ∨ (P' = 0 ∧ Q' = 1) ∨ (P' = 1 ∧ Q' = 1) ∨ (P' = 2 ∧ Q' = 1) ∨
          (P' = 3 ∧ Q' = 1) ∨ (P' = 3 ∧ Q' = 2)) ∨
        ((P' = -1 ∧ Q' = 0) ∨ (P' = 0 ∧ Q' = -1) ∨ (P' = -1 ∧ Q' = -1) ∨ (P' = -2 ∧ Q' = -1) ∨
          (P' = -3 ∧ Q' = -1) ∨ (P' = -3 ∧ Q' = -2)) := by
    intro x y p q p' q' hx hy α dS dT h
    apply hcoeff
    rw [← h, hx, hy]
    module
  have noopp : ∀ {x y : J} {p q p' q' : ℤ}, P.root x = p • P.root a + q • P.root c →
      P.root y = p' • P.root a + q' • P.root c → (p + p' ≠ 0 ∨ q + q' ≠ 0) →
      P.root x ≠ -P.root y := by
    intro x y p q p' q' hx hy hpq h
    have h0 : (p + p') • P.root a + (q + q') • P.root c = 0 := by
      have : P.root x + P.root y = 0 := by rw [h, neg_add_cancel]
      rw [hx, hy] at this
      rw [← this]
      module
    have := LinearIndependent.pair_iff.mp hli _ _ h0
    omega
  -- distinctness of the indices
  have hd₁₂ : d₁ ≠ d₂ := hdist rd₁ rd₂ (by omega)
  have hd₁₃ : d₁ ≠ d₃ := hdist rd₁ rd₃ (by omega)
  have hd₁₄ : d₁ ≠ d₄ := hdist rd₁ rd₄ (by omega)
  have hd₂₃ : d₂ ≠ d₃ := hdist rd₂ rd₃ (by omega)
  have hd₂₄ : d₂ ≠ d₄ := hdist rd₂ rd₄ (by omega)
  have hd₃₄ : d₃ ≠ d₄ := hdist rd₃ rd₄ (by omega)
  have hd₁a : d₁ ≠ a := hdist rd₁ ra (by omega)
  have hd₂a : d₂ ≠ a := hdist rd₂ ra (by omega)
  have hd₃a : d₃ ≠ a := hdist rd₃ ra (by omega)
  have hd₄a : d₄ ≠ a := hdist rd₄ ra (by omega)
  have hd₁c : d₁ ≠ c := hdist rd₁ rc (by omega)
  have hd₂c : d₂ ≠ c := hdist rd₂ rc (by omega)
  have hd₃c : d₃ ≠ c := hdist rd₃ rc (by omega)
  have hd₄c : d₄ ≠ c := hdist rd₄ rc (by omega)
  have hd₁na : d₁ ≠ na := hdist rd₁ rna (by omega)
  have hd₂na : d₂ ≠ na := hdist rd₂ rna (by omega)
  have hd₃na : d₃ ≠ na := hdist rd₃ rna (by omega)
  have hd₄na : d₄ ≠ na := hdist rd₄ rna (by omega)
  have hd₁nc : d₁ ≠ nc := hdist rd₁ rnc (by omega)
  have hd₂nc : d₂ ≠ nc := hdist rd₂ rnc (by omega)
  have hd₃nc : d₃ ≠ nc := hdist rd₃ rnc (by omega)
  have hd₄nc : d₄ ≠ nc := hdist rd₄ rnc (by omega)
  -- the four conjugated parametrizations
  have hp₁ : IsRootParametrization i (P.root d₁) p₁ := by
    have h := (hv a).comp_innerIso hnc
    rw [hd₁_def, RootPairing.root_reflectionPerm]
    exact h
  have hp₂ : IsRootParametrization i (P.root d₂) p₂ := by
    have h := hp₁.comp_innerIso hna
    rw [hd₂_def, RootPairing.root_reflectionPerm]
    exact h
  have hp₃ : IsRootParametrization i (P.root d₃) p₃ := by
    have h := (hv c).comp_innerIso hna
    rw [hd₃_def, RootPairing.root_reflectionPerm]
    exact h
  have hp₄ : IsRootParametrization i (P.root d₄) p₄ := by
    have h := hp₃.comp_innerIso hnc
    rw [hd₄_def, RootPairing.root_reflectionPerm]
    exact h
  let v' : J → (Ga R ⟶ G) :=
    Function.update (Function.update (Function.update (Function.update v d₁ p₁) d₂ p₂) d₃ p₃)
      d₄ p₄
  have hv'_eq : ∀ x, v' x = if x = d₄ then p₄ else if x = d₃ then p₃ else
      if x = d₂ then p₂ else if x = d₁ then p₁ else v x := by
    intro x
    simp only [v', Function.update_apply]
  have hv'd₁ : v' d₁ = p₁ := by
    rw [hv'_eq]; simp [hd₁₂, hd₁₃, hd₁₄]
  have hv'd₂ : v' d₂ = p₂ := by
    rw [hv'_eq]; simp [hd₂₃, hd₂₄]
  have hv'd₃ : v' d₃ = p₃ := by
    rw [hv'_eq]; simp [hd₃₄]
  have hv'd₄ : v' d₄ = p₄ := by
    rw [hv'_eq]; simp
  have hv'o : ∀ x, x ≠ d₁ → x ≠ d₂ → x ≠ d₃ → x ≠ d₄ → v' x = v x := by
    intro x h₁ h₂ h₃ h₄
    rw [hv'_eq]; simp [h₁, h₂, h₃, h₄]
  have hv'a : v' a = v a := hv'o a (Ne.symm hd₁a) (Ne.symm hd₂a) (Ne.symm hd₃a) (Ne.symm hd₄a)
  have hv'c : v' c = v c := hv'o c (Ne.symm hd₁c) (Ne.symm hd₂c) (Ne.symm hd₃c) (Ne.symm hd₄c)
  have hv'na : v' na = v na :=
    hv'o na (Ne.symm hd₁na) (Ne.symm hd₂na) (Ne.symm hd₃na) (Ne.symm hd₄na)
  have hv'nc : v' nc = v nc :=
    hv'o nc (Ne.symm hd₁nc) (Ne.symm hd₂nc) (Ne.symm hd₃nc) (Ne.symm hd₄nc)
  have hv' : ∀ α, IsRootParametrization i (P.root α) (v' α) := by
    intro α
    rw [hv'_eq]
    split_ifs with h₄ h₃ h₂ h₁
    · subst h₄; exact hp₄
    · subst h₃; exact hp₃
    · subst h₂; exact hp₂
    · subst h₁; exact hp₁
    · exact hv α
  -- commutations
  have comm_of : ∀ {x y : J} {p q p' q' : ℤ} (hx : P.root x = p • P.root a + q • P.root c)
      (hy : P.root y = p' • P.root a + q' • P.root c), (p + p' ≠ 0 ∨ q + q' ≠ 0) →
      (∀ dS dT : ℤ, 1 ≤ dS → 1 ≤ dT →
        let P' := dS * p + dT * p'
        let Q' := dS * q + dT * q'
        ¬ (((P' = 1 ∧ Q' = 0) ∨ (P' = 0 ∧ Q' = 1) ∨ (P' = 1 ∧ Q' = 1) ∨ (P' = 2 ∧ Q' = 1) ∨
          (P' = 3 ∧ Q' = 1) ∨ (P' = 3 ∧ Q' = 2)) ∨
        ((P' = -1 ∧ Q' = 0) ∨ (P' = 0 ∧ Q' = -1) ∨ (P' = -1 ∧ Q' = -1) ∨ (P' = -2 ∧ Q' = -1) ∨
          (P' = -3 ∧ Q' = -1) ∨ (P' = -3 ∧ Q' = -2)))) →
      ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
        (z w : Γ((Over.mk s).left, ⊤)),
        rootPoint (v' x) (Over.mk s) z * rootPoint (v' y) (Over.mk s) w =
          rootPoint (v' y) (Over.mk s) w * rootPoint (v' x) (Over.mk s) z := by
    intro x y p q p' q' hx hy hne hcone B _ s z w
    refine rootPoint_commute_of_forall_ne hG hmax hP hv' (noopp hx hy hne) ?_ s z w
    intro α dS dT hS hT h
    exact hcone dS dT (by exact_mod_cast hS) (by exact_mod_cast hT) (cone_gen hx hy α dS dT h)
  have cm_nc_a := comm_of rnc ra (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_c_d₁ := comm_of rc rd₁ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_c_d₂ := comm_of rc rd₂ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_c_d₄ := comm_of rc rd₄ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_nc_d₂ := comm_of rnc rd₂ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_nc_d₃ := comm_of rnc rd₃ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_d₂_d₃ := comm_of rd₂ rd₃ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_d₂_d₄ := comm_of rd₂ rd₄ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_d₃_d₄ := comm_of rd₃ rd₄ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_na_c := comm_of rna rc (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_d₁_d₃ := comm_of rd₁ rd₃ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_d₁_d₄ := comm_of rd₁ rd₄ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_a_d₄ := comm_of ra rd₄ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_na_d₄ := comm_of rna rd₄ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  -- positivity in `b`
  have hapos : b.IsPos a := b.isPos_of_mem_support ha
  have hcpos : b.IsPos c := b.isPos_of_mem_support hc
  have rd₁' : P.root d₁ = P.root a + P.root c := by rw [rd₁, one_smul, one_smul]
  have rd₂' : P.root d₂ = P.root a + P.root d₁ := by rw [rd₂, rd₁]; module
  have rd₃' : P.root d₃ = P.root a + P.root d₂ := by rw [rd₃, rd₂]; module
  have rd₄' : P.root d₄ = P.root c + P.root d₃ := by rw [rd₄, rd₃]; module
  have hd₁pos : b.IsPos d₁ := hapos.add hcpos rd₁'
  have hd₂pos : b.IsPos d₂ := hapos.add hd₁pos rd₂'
  have hd₃pos : b.IsPos d₃ := hapos.add hd₂pos rd₃'
  have hd₄pos : b.IsPos d₄ := hcpos.add hd₃pos rd₄'
  have hsame' : ∀ {x y : J} {p q p' q' : ℤ}, P.root x = p • P.root a + q • P.root c →
      P.root y = p' • P.root a + q' • P.root c → p = p' → q = q' → x = y := by
    intro x y p q p' q' hx hy hp hq
    subst hp hq
    exact hsame hx hy
  -- the commutator of `a` and `c`
  obtain ⟨K₁, hK₁⟩ := exists_rootPoint_comm_cone hG hmax hP hv' (β := a) (ε := c)
    (noopp ra rc (by omega)) hac [d₁, d₂, d₃, d₄]
    (by simp [hd₁₂, hd₁₃, hd₁₄, hd₂₃, hd₂₄, hd₃₄]) ![(1, 1), (2, 1), (3, 1), (3, 2)]
    (by intro r; fin_cases r <;> simp [rd₁, rd₂, rd₃, rd₄])
    (by intro r; fin_cases r <;> simp)
    (by
      intro α dS dT hS hT h
      have hα : P.root α = (dS : ℤ) • P.root a + (dT : ℤ) • P.root c := h.symm
      have := hcoeff hα
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases (show ((dS : ℤ) = 1 ∧ (dT : ℤ) = 1) ∨ ((dS : ℤ) = 2 ∧ (dT : ℤ) = 1) ∨
          ((dS : ℤ) = 3 ∧ (dT : ℤ) = 1) ∨ ((dS : ℤ) = 3 ∧ (dT : ℤ) = 2) by omega) with
        ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl (hsame' hα rd₁ e1 e2)
      · exact Or.inr (Or.inl (hsame' hα rd₂ e1 e2))
      · exact Or.inr (Or.inr (Or.inl (hsame' hα rd₃ e1 e2)))
      · exact Or.inr (Or.inr (Or.inr (hsame' hα rd₄ e1 e2))))
  simp only [List.length_cons, List.length_nil, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, mul_one, List.get_eq_getElem, Fin.val_succ, Fin.val_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, pow_one, hv'a, hv'c, hv'd₁, hv'd₂, hv'd₃, hv'd₄] at hK₁
  generalize K₁ 0 = k₀ at hK₁
  generalize K₁ (Fin.succ 0) = k₁ at hK₁
  generalize K₁ (Fin.succ 0).succ = k₂ at hK₁
  generalize K₁ (Fin.succ 0).succ.succ = k₃ at hK₁
  -- the commutator of `a` and `a + c`
  have rd₂'' : P.root d₂ = (1 : ℤ) • P.root a + (1 : ℤ) • P.root d₁ := by rw [rd₂, rd₁]; module
  have rd₃'' : P.root d₃ = (2 : ℤ) • P.root a + (1 : ℤ) • P.root d₁ := by rw [rd₃, rd₁]; module
  have rd₄'' : P.root d₄ = (1 : ℤ) • P.root a + (2 : ℤ) • P.root d₁ := by rw [rd₄, rd₁]; module
  obtain ⟨K₂, hK₂⟩ := exists_rootPoint_comm_cone hG hmax hP hv' (β := a) (ε := d₁)
    (noopp ra rd₁ (by omega)) (Ne.symm hd₁a) [d₂, d₃, d₄]
    (by simp [hd₂₃, hd₂₄, hd₃₄]) ![(1, 1), (2, 1), (1, 2)]
    (by intro r; fin_cases r <;> simp [rd₂'', rd₃'', rd₄''])
    (by intro r; fin_cases r <;> simp)
    (by
      intro α dS dT hS hT h
      have hα : P.root α = ((dS : ℤ) + dT) • P.root a + (dT : ℤ) • P.root c := by
        rw [← h, rd₁]; module
      have := hcoeff hα
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases (show ((dS : ℤ) = 1 ∧ (dT : ℤ) = 1) ∨ ((dS : ℤ) = 2 ∧ (dT : ℤ) = 1) ∨
          ((dS : ℤ) = 1 ∧ (dT : ℤ) = 2) by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl (hsame' hα rd₂ (by omega) (by omega))
      · exact Or.inr (Or.inl (hsame' hα rd₃ (by omega) (by omega)))
      · exact Or.inr (Or.inr (hsame' hα rd₄ (by omega) (by omega))))
  simp only [List.length_cons, List.length_nil, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, mul_one, List.get_eq_getElem, Fin.val_succ, Fin.val_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, pow_one, hv'a, hv'd₁, hv'd₂, hv'd₃, hv'd₄] at hK₂
  generalize K₂ 0 = l₀ at hK₂
  generalize K₂ (Fin.succ 0) = l₁ at hK₂
  generalize K₂ (Fin.succ 0).succ = l₂ at hK₂
  -- the single commutators
  obtain ⟨kH, hkH'⟩ := exists_rootPoint_comm_single hG hmax hP hv' (β := a) (ε := d₂) (δ := d₃)
    (noopp ra rd₂ (by omega)) rd₃'
    (by
      intro α dS dT hS hT h
      have := cone_gen ra rd₂ α dS dT h
      simp only at this
      omega)
  simp only [hv'a, hv'd₂, hv'd₃] at hkH'
  obtain ⟨kJ, hkJ'⟩ := exists_rootPoint_comm_single hG hmax hP hv' (β := c) (ε := d₃) (δ := d₄)
    (noopp rc rd₃ (by omega)) rd₄'
    (by
      intro α dS dT hS hT h
      have := cone_gen rc rd₃ α dS dT h
      simp only at this
      omega)
  simp only [hv'c, hv'd₃, hv'd₄] at hkJ'
  have rd₄''' : P.root d₄ = P.root d₁ + P.root d₂ := by rw [rd₄, rd₁, rd₂]; module
  obtain ⟨k₅, hK₅⟩ := exists_rootPoint_comm_single hG hmax hP hv' (β := d₁) (ε := d₂) (δ := d₄)
    (noopp rd₁ rd₂ (by omega)) rd₄'''
    (by
      intro α dS dT hS hT h
      have := cone_gen rd₁ rd₂ α dS dT h
      simp only at this
      omega)
  simp only [hv'd₁, hv'd₂, hv'd₄] at hK₅
  -- the definitions of `p₁, …, p₄` as conjugates
  have hdef₁ : ∀ (Z : Over (Spec (CommRingCat.of R))) (t : Γ(Z.left, ⊤)),
      rootPoint p₁ Z t = G.constantPoint Nc Z * rootPoint (v a) Z t * (G.constantPoint Nc Z)⁻¹ := by
    intro Z t
    rw [hp₁_def, rootPoint_comp, GroupScheme.comp_innerIso_hom]
  have hdef₂ : ∀ (Z : Over (Spec (CommRingCat.of R))) (t : Γ(Z.left, ⊤)),
      rootPoint p₂ Z t = G.constantPoint Na Z * rootPoint p₁ Z t * (G.constantPoint Na Z)⁻¹ := by
    intro Z t
    rw [hp₂_def, rootPoint_comp, GroupScheme.comp_innerIso_hom]
  have hdef₃ : ∀ (Z : Over (Spec (CommRingCat.of R))) (t : Γ(Z.left, ⊤)),
      rootPoint p₃ Z t = G.constantPoint Na Z * rootPoint (v c) Z t * (G.constantPoint Na Z)⁻¹ := by
    intro Z t
    rw [hp₃_def, rootPoint_comp, GroupScheme.comp_innerIso_hom]
  have hdef₄ : ∀ (Z : Over (Spec (CommRingCat.of R))) (t : Γ(Z.left, ⊤)),
      rootPoint p₄ Z t = G.constantPoint Nc Z * rootPoint p₃ Z t * (G.constantPoint Nc Z)⁻¹ := by
    intro Z t
    rw [hp₄_def, rootPoint_comp, GroupScheme.comp_innerIso_hom]
  -- pairings and signs
  have pnaa : P.pairingIn ℤ na a = -2 := by
    rw [hpI, hpair rna a, RootPairing.pairing_same]
    norm_num
  have pd₁a : P.pairingIn ℤ d₁ a = -1 := by rw [hpI, hpd₁a]
  have pd₃c : P.pairingIn ℤ d₃ c = -1 := by rw [hpI, hpd₃c]
  -- evaluation over `R` itself
  set s₀ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R) := 𝟙 _ with hs₀
  obtain ⟨ε, hε⟩ : ∃ ε : R →+* Γ((Over.mk s₀).left, ⊤),
      ∀ r, ε r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv r :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom, fun r => rfl⟩
  have hpre : ∀ r : R, (Spec.preimage s₀).hom r = r := by
    intro r
    rw [hs₀, Spec.preimage_id]
    rfl
  have hsurj : ∀ t : Γ((Over.mk s₀).left, ⊤), ∃ r : R, ε r = t := by
    intro t
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom t, ?_⟩
    rw [hε]
    exact Iso.hom_inv_id_apply _ _
  have hεinj : ∀ r r' : R, ε r = ε r' → r = r' := by
    intro r r' h
    rw [hε, hε] at h
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom h
    rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at this
  have sgn_odd : ∀ k : ℤ, Odd k → ∀ t : Γ((Over.mk s₀).left, ⊤), k.negOnePow • t = -t := by
    intro k hk t
    rw [Int.negOnePow_odd k hk, Units.neg_smul, one_smul]
  have sgn_even : ∀ k : ℤ, Even k → ∀ t : Γ((Over.mk s₀).left, ⊤), k.negOnePow • t = t := by
    intro k hk t
    rw [Int.negOnePow_even k hk, one_smul]
  -- the commutator formulas over `R`
  have F1 : ∀ x y : Γ((Over.mk s₀).left, ⊤),
      rootPoint (v c) (Over.mk s₀) y * rootPoint (v a) (Over.mk s₀) x =
        rootPoint (v a) (Over.mk s₀) x * rootPoint (v c) (Over.mk s₀) y *
          rootPoint p₁ (Over.mk s₀) (ε k₀ * x * y) * rootPoint p₂ (Over.mk s₀) (ε k₁ * x ^ 2 * y) *
          rootPoint p₃ (Over.mk s₀) (ε k₂ * x ^ 3 * y) *
          rootPoint p₄ (Over.mk s₀) (ε k₃ * x ^ 3 * y ^ 2) := by
    intro x y
    obtain ⟨x₀, rfl⟩ := hsurj x
    obtain ⟨y₀, rfl⟩ := hsurj y
    have h := hK₁ R s₀ x₀ y₀
    simp only [hpre, map_mul, map_pow] at h
    simp only [← hε] at h
    rw [inv_mul_eq_iff_eq_mul] at h
    rw [h]
    simp only [mul_assoc]
    try rfl
  have F2 : ∀ x y : Γ((Over.mk s₀).left, ⊤),
      rootPoint p₁ (Over.mk s₀) y * rootPoint (v a) (Over.mk s₀) x =
        rootPoint (v a) (Over.mk s₀) x * rootPoint p₁ (Over.mk s₀) y *
          rootPoint p₂ (Over.mk s₀) (ε l₀ * x * y) * rootPoint p₃ (Over.mk s₀) (ε l₁ * x ^ 2 * y) *
          rootPoint p₄ (Over.mk s₀) (ε l₂ * x * y ^ 2) := by
    intro x y
    obtain ⟨x₀, rfl⟩ := hsurj x
    obtain ⟨y₀, rfl⟩ := hsurj y
    have h := hK₂ R s₀ x₀ y₀
    simp only [hpre, map_mul, map_pow] at h
    simp only [← hε] at h
    rw [inv_mul_eq_iff_eq_mul] at h
    rw [h]
    simp only [mul_assoc]
    try rfl
  have F3 : ∀ x y : Γ((Over.mk s₀).left, ⊤),
      rootPoint p₂ (Over.mk s₀) y * rootPoint (v a) (Over.mk s₀) x =
        rootPoint (v a) (Over.mk s₀) x * rootPoint p₂ (Over.mk s₀) y * rootPoint p₃ (Over.mk s₀) (ε
            kH * x * y) := by
    intro x y
    obtain ⟨x₀, rfl⟩ := hsurj x
    obtain ⟨y₀, rfl⟩ := hsurj y
    have h := hkH' R s₀ x₀ y₀
    simp only [hpre, map_mul] at h
    simp only [← hε] at h
    rw [inv_mul_eq_iff_eq_mul] at h
    rw [h]
    try rfl
  have F4 : ∀ x y : Γ((Over.mk s₀).left, ⊤),
      rootPoint p₃ (Over.mk s₀) y * rootPoint (v c) (Over.mk s₀) x =
        rootPoint (v c) (Over.mk s₀) x * rootPoint p₃ (Over.mk s₀) y * rootPoint p₄ (Over.mk s₀) (ε
            kJ * x * y) := by
    intro x y
    obtain ⟨x₀, rfl⟩ := hsurj x
    obtain ⟨y₀, rfl⟩ := hsurj y
    have h := hkJ' R s₀ x₀ y₀
    simp only [hpre, map_mul] at h
    simp only [← hε] at h
    rw [inv_mul_eq_iff_eq_mul] at h
    rw [h]
    try rfl
  have F5 : ∀ x y : Γ((Over.mk s₀).left, ⊤),
      rootPoint p₂ (Over.mk s₀) y * rootPoint p₁ (Over.mk s₀) x =
        rootPoint p₁ (Over.mk s₀) x * rootPoint p₂ (Over.mk s₀) y * rootPoint p₄ (Over.mk s₀) (ε k₅
            * x * y) := by
    intro x y
    obtain ⟨x₀, rfl⟩ := hsurj x
    obtain ⟨y₀, rfl⟩ := hsurj y
    have h := hK₅ R s₀ x₀ y₀
    simp only [hpre, map_mul] at h
    simp only [← hε] at h
    rw [inv_mul_eq_iff_eq_mul] at h
    rw [h]
    try rfl
  -- commutations over `R`
  have cr : ∀ {x y : J} {f g : Ga R ⟶ G}, v' x = f → v' y = g →
      (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
        (z w : Γ((Over.mk s).left, ⊤)),
        rootPoint (v' x) (Over.mk s) z * rootPoint (v' y) (Over.mk s) w =
          rootPoint (v' y) (Over.mk s) w * rootPoint (v' x) (Over.mk s) z) →
      ∀ z w : Γ((Over.mk s₀).left, ⊤), rootPoint f (Over.mk s₀) z * rootPoint g (Over.mk s₀) w =
          rootPoint g (Over.mk s₀) w * rootPoint f (Over.mk s₀) z := by
    intro x y f g hx hy h z w
    have := h R s₀ z w
    rwa [hx, hy] at this
  have hnba : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint (v nc) (Over.mk s₀) x * rootPoint (v a)
      (Over.mk s₀) y = rootPoint (v a) (Over.mk s₀) y * rootPoint (v nc) (Over.mk s₀) x :=
    cr hv'nc hv'a cm_nc_a
  have hb1 : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint (v c) (Over.mk s₀) x * rootPoint p₁
      (Over.mk s₀) y = rootPoint p₁ (Over.mk s₀) y * rootPoint (v c) (Over.mk s₀) x :=
    cr hv'c hv'd₁ cm_c_d₁
  have hb2 : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint (v c) (Over.mk s₀) x * rootPoint p₂
      (Over.mk s₀) y = rootPoint p₂ (Over.mk s₀) y * rootPoint (v c) (Over.mk s₀) x :=
    cr hv'c hv'd₂ cm_c_d₂
  have hb4 : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint (v c) (Over.mk s₀) x * rootPoint p₄
      (Over.mk s₀) (-y) = rootPoint p₄ (Over.mk s₀) (-y) * rootPoint (v c) (Over.mk s₀) x :=
    fun x y => cr hv'c hv'd₄ cm_c_d₄ x (-y)
  have hnb2 : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint (v nc) (Over.mk s₀) x * rootPoint p₂
      (Over.mk s₀) y = rootPoint p₂ (Over.mk s₀) y * rootPoint (v nc) (Over.mk s₀) x :=
    cr hv'nc hv'd₂ cm_nc_d₂
  have hnb3 : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint (v nc) (Over.mk s₀) x * rootPoint p₃
      (Over.mk s₀) (-y) = rootPoint p₃ (Over.mk s₀) (-y) * rootPoint (v nc) (Over.mk s₀) x :=
    fun x y => cr hv'nc hv'd₃ cm_nc_d₃ x (-y)
  have h23 : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint p₂ (Over.mk s₀) x * rootPoint p₃ (Over.mk
      s₀) (-y) = rootPoint p₃ (Over.mk s₀) (-y) * rootPoint p₂ (Over.mk s₀) x :=
    fun x y => cr hv'd₂ hv'd₃ cm_d₂_d₃ x (-y)
  have h24 : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint p₂ (Over.mk s₀) x * rootPoint p₄ (Over.mk
      s₀) (-y) = rootPoint p₄ (Over.mk s₀) (-y) * rootPoint p₂ (Over.mk s₀) x :=
    fun x y => cr hv'd₂ hv'd₄ cm_d₂_d₄ x (-y)
  have h34 : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint p₃ (Over.mk s₀) (-x) * rootPoint p₄
      (Over.mk s₀) (-y) = rootPoint p₄ (Over.mk s₀) (-y) * rootPoint p₃ (Over.mk s₀) (-x) :=
    fun x y => cr hv'd₃ hv'd₄ cm_d₃_d₄ (-x) (-y)
  have hnab : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint (v na) (Over.mk s₀) x * rootPoint (v c)
      (Over.mk s₀) y = rootPoint (v c) (Over.mk s₀) y * rootPoint (v na) (Over.mk s₀) x :=
    cr hv'na hv'c cm_na_c
  have h13 : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint p₁ (Over.mk s₀) x * rootPoint p₃ (Over.mk
      s₀) (-y) = rootPoint p₃ (Over.mk s₀) (-y) * rootPoint p₁ (Over.mk s₀) x :=
    fun x y => cr hv'd₁ hv'd₃ cm_d₁_d₃ x (-y)
  have h14 : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint p₁ (Over.mk s₀) x * rootPoint p₄ (Over.mk
      s₀) (-y) = rootPoint p₄ (Over.mk s₀) (-y) * rootPoint p₁ (Over.mk s₀) x :=
    fun x y => cr hv'd₁ hv'd₄ cm_d₁_d₄ x (-y)
  have hna4 : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint (v na) (Over.mk s₀) x * rootPoint p₄
      (Over.mk s₀) y = rootPoint p₄ (Over.mk s₀) y * rootPoint (v na) (Over.mk s₀) x :=
    cr hv'na hv'd₄ cm_na_d₄
  have ha4 : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint (v a) (Over.mk s₀) x * rootPoint p₄
      (Over.mk s₀) y = rootPoint p₄ (Over.mk s₀) y * rootPoint (v a) (Over.mk s₀) x :=
    cr hv'a hv'd₄ cm_a_d₄
  -- the Weyl points over `R`
  have hNaZ : G.constantPoint Na (Over.mk s₀) = rootPoint (v na) (Over.mk s₀) (-1) * rootPoint (v
      a) (Over.mk s₀) 1 * rootPoint (v na) (Over.mk s₀) (-1) := by
    rw [hNa_def]
    exact constantPoint_weylPoint _ _ _
  have hNcZ : G.constantPoint Nc (Over.mk s₀) = rootPoint (v nc) (Over.mk s₀) (-1) * rootPoint (v
      c) (Over.mk s₀) 1 * rootPoint (v nc) (Over.mk s₀) (-1) := by
    rw [hNc_def]
    exact constantPoint_weylPoint _ _ _
  have conjm : ∀ (N x y : (Over.mk s₀) ⟶ G.X), N * (x * y) * N⁻¹ = (N * x * N⁻¹) * (N * y * N⁻¹) :=
      by
    intro N x y
    group
  -- conjugation by `N_c`
  have cba : ∀ x : Γ((Over.mk s₀).left, ⊤), G.constantPoint Nc (Over.mk s₀) * rootPoint (v a)
      (Over.mk s₀) x * (G.constantPoint Nc (Over.mk s₀))⁻¹ = rootPoint p₁ (Over.mk s₀) x :=
    fun x => (hdef₁ _ x).symm
  have cbb : ∀ y : Γ((Over.mk s₀).left, ⊤), G.constantPoint Nc (Over.mk s₀) * rootPoint (v c)
      (Over.mk s₀) y * (G.constantPoint Nc (Over.mk s₀))⁻¹ = rootPoint (v nc) (Over.mk s₀) (-y) :=
    fun y => hROc R s₀ y
  have cb1 : ∀ t : Γ((Over.mk s₀).left, ⊤), G.constantPoint Nc (Over.mk s₀) * rootPoint p₁ (Over.mk
      s₀) t * (G.constantPoint Nc (Over.mk s₀))⁻¹ = rootPoint (v a) (Over.mk s₀) (-t) := by
    intro t
    have h := hsqc a (v a) (hv a) R s₀ t
    rw [h1, sgn_odd (-1) ⟨-1, by norm_num⟩] at h
    rw [hdef₁, ← h]
    group
  have cb2 : ∀ t : Γ((Over.mk s₀).left, ⊤), G.constantPoint Nc (Over.mk s₀) * rootPoint p₂ (Over.mk
      s₀) t * (G.constantPoint Nc (Over.mk s₀))⁻¹ = rootPoint p₂ (Over.mk s₀) t := by
    intro t
    have hcm : Commute (G.constantPoint Nc (Over.mk s₀)) (rootPoint p₂ (Over.mk s₀) t) := by
      rw [hNcZ]
      exact (Commute.mul_left (Commute.mul_left (hnb2 _ _) (hb2 _ _)) (hnb2 _ _))
    rw [hcm.eq, mul_inv_cancel_right]
  have cb3 : ∀ t : Γ((Over.mk s₀).left, ⊤), G.constantPoint Nc (Over.mk s₀) * rootPoint p₃ (Over.mk
      s₀) (-t) * (G.constantPoint Nc (Over.mk s₀))⁻¹ = rootPoint p₄ (Over.mk s₀) (-t) :=
    fun t => (hdef₄ _ (-t)).symm
  have cb4 : ∀ t : Γ((Over.mk s₀).left, ⊤), G.constantPoint Nc (Over.mk s₀) * rootPoint p₄ (Over.mk
      s₀) (-t) * (G.constantPoint Nc (Over.mk s₀))⁻¹ = rootPoint p₃ (Over.mk s₀) (-(-t)) := by
    intro t
    have h := hsqc d₃ p₃ hp₃ R s₀ (-t)
    rw [pd₃c, sgn_odd (-1) ⟨-1, by norm_num⟩] at h
    rw [hdef₄, ← h]
    group
  -- conjugation by `N_a`
  have caa : ∀ x : Γ((Over.mk s₀).left, ⊤), G.constantPoint Na (Over.mk s₀) * rootPoint (v a)
      (Over.mk s₀) x * (G.constantPoint Na (Over.mk s₀))⁻¹ = rootPoint (v na) (Over.mk s₀) (-x) :=
    fun x => hROa R s₀ x
  have cana : ∀ x : Γ((Over.mk s₀).left, ⊤), G.constantPoint Na (Over.mk s₀) * rootPoint (v na)
      (Over.mk s₀) x * (G.constantPoint Na (Over.mk s₀))⁻¹ = rootPoint (v a) (Over.mk s₀) (-x) := by
    intro x
    have hs := hsqa na (v na) (hv na) R s₀ x
    rw [pnaa, sgn_even (-2) ⟨-1, by norm_num⟩] at hs
    calc G.constantPoint Na (Over.mk s₀) * rootPoint (v na) (Over.mk s₀) x * (G.constantPoint Na
        (Over.mk s₀))⁻¹
        = (G.constantPoint Na (Over.mk s₀))⁻¹ * ((G.constantPoint Na (Over.mk s₀) * G.constantPoint
            Na (Over.mk s₀)) * rootPoint (v na) (Over.mk s₀) x *
            (G.constantPoint Na (Over.mk s₀) * G.constantPoint Na (Over.mk s₀))⁻¹) *
                G.constantPoint Na (Over.mk s₀) := by group
      _ = (G.constantPoint Na (Over.mk s₀))⁻¹ * rootPoint (v na) (Over.mk s₀) x * G.constantPoint
          Na (Over.mk s₀) := by rw [hs]
      _ = (G.constantPoint Na (Over.mk s₀))⁻¹ * (G.constantPoint Na (Over.mk s₀) * rootPoint (v a)
          (Over.mk s₀) (-x) * (G.constantPoint Na (Over.mk s₀))⁻¹) * G.constantPoint Na (Over.mk
          s₀) := by
          rw [hROa R s₀ (-x), neg_neg]
      _ = rootPoint (v a) (Over.mk s₀) (-x) := by group
  have cab : ∀ y : Γ((Over.mk s₀).left, ⊤), G.constantPoint Na (Over.mk s₀) * rootPoint (v c)
      (Over.mk s₀) y * (G.constantPoint Na (Over.mk s₀))⁻¹ = rootPoint p₃ (Over.mk s₀) (-(-y)) := by
    intro y
    rw [neg_neg, hdef₃]
  have ca1 : ∀ t : Γ((Over.mk s₀).left, ⊤), G.constantPoint Na (Over.mk s₀) * rootPoint p₁ (Over.mk
      s₀) t * (G.constantPoint Na (Over.mk s₀))⁻¹ = rootPoint p₂ (Over.mk s₀) t :=
    fun t => (hdef₂ _ t).symm
  have ca2 : ∀ t : Γ((Over.mk s₀).left, ⊤), G.constantPoint Na (Over.mk s₀) * rootPoint p₂ (Over.mk
      s₀) t * (G.constantPoint Na (Over.mk s₀))⁻¹ = rootPoint p₁ (Over.mk s₀) (-t) := by
    intro t
    have h := hsqa d₁ p₁ hp₁ R s₀ t
    rw [pd₁a, sgn_odd (-1) ⟨-1, by norm_num⟩] at h
    rw [hdef₂, ← h]
    group
  have ca3 : ∀ t : Γ((Over.mk s₀).left, ⊤), G.constantPoint Na (Over.mk s₀) * rootPoint p₃ (Over.mk
      s₀) (-t) * (G.constantPoint Na (Over.mk s₀))⁻¹ = rootPoint (v c) (Over.mk s₀) t := by
    intro t
    have h := hsqa c (v c) (hv c) R s₀ (-t)
    rw [h2, sgn_odd (-3) ⟨-2, by norm_num⟩, neg_neg] at h
    rw [hdef₃, ← h]
    group
  have ca4 : ∀ t : Γ((Over.mk s₀).left, ⊤), G.constantPoint Na (Over.mk s₀) * rootPoint p₄ (Over.mk
      s₀) (-t) * (G.constantPoint Na (Over.mk s₀))⁻¹ = rootPoint p₄ (Over.mk s₀) (-t) := by
    intro t
    have hcm : Commute (G.constantPoint Na (Over.mk s₀)) (rootPoint p₄ (Over.mk s₀) (-t)) := by
      rw [hNaZ]
      exact (Commute.mul_left (Commute.mul_left (hna4 _ _) (ha4 _ _)) (hna4 _ _))
    rw [hcm.eq, mul_inv_cancel_right]
  -- additivity
  have hP3' : ∀ s t : Γ((Over.mk s₀).left, ⊤), rootPoint p₃ (Over.mk s₀) (-(s + t)) = rootPoint p₃
      (Over.mk s₀) (-s) * rootPoint p₃ (Over.mk s₀) (-t) := by
    intro s t
    rw [neg_add, rootPoint_add]
  have hP4' : ∀ s t : Γ((Over.mk s₀).left, ⊤), rootPoint p₄ (Over.mk s₀) (-(s + t)) = rootPoint p₄
      (Over.mk s₀) (-s) * rootPoint p₄ (Over.mk s₀) (-t) := by
    intro s t
    rw [neg_add, rootPoint_add]
  -- the commutator formulas in the form of the abstract identities
  have h1' : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint (v c) (Over.mk s₀) y * rootPoint (v a)
      (Over.mk s₀) x =
      rootPoint (v a) (Over.mk s₀) x * rootPoint (v c) (Over.mk s₀) y * rootPoint p₁ (Over.mk s₀)
          (ε k₀ * x * y) * rootPoint p₂ (Over.mk s₀) (ε k₁ * x ^ 2 * y) *
        rootPoint p₃ (Over.mk s₀) (-(-ε k₂ * x ^ 3 * y)) * rootPoint p₄ (Over.mk s₀) (-(-ε k₃ * x ^
            3 * y ^ 2)) := by
    intro x y
    rw [F1]
    simp only [neg_mul, neg_neg]
  have h2' : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint p₁ (Over.mk s₀) y * rootPoint (v a)
      (Over.mk s₀) x =
      rootPoint (v a) (Over.mk s₀) x * rootPoint p₁ (Over.mk s₀) y * rootPoint p₂ (Over.mk s₀) (ε
          l₀ * x * y) * rootPoint p₃ (Over.mk s₀) (-(-ε l₁ * x ^ 2 * y)) *
        rootPoint p₄ (Over.mk s₀) (-(-ε l₂ * x * y ^ 2)) := by
    intro x y
    rw [F2]
    simp only [neg_mul, neg_neg]
  have h3' : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint p₂ (Over.mk s₀) y * rootPoint (v a)
      (Over.mk s₀) x =
      rootPoint (v a) (Over.mk s₀) x * rootPoint p₂ (Over.mk s₀) y * rootPoint p₃ (Over.mk s₀)
          (-(-ε kH * x * y)) := by
    intro x y
    rw [F3]
    simp only [neg_mul, neg_neg]
  have h4' : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint p₃ (Over.mk s₀) (-y) * rootPoint (v c)
      (Over.mk s₀) x =
      rootPoint (v c) (Over.mk s₀) x * rootPoint p₃ (Over.mk s₀) (-y) * rootPoint p₄ (Over.mk s₀)
          (-(ε kJ * x * y)) := by
    intro x y
    rw [F4, mul_neg]
  have h6' : ∀ x y : Γ((Over.mk s₀).left, ⊤), rootPoint p₂ (Over.mk s₀) y * rootPoint p₁ (Over.mk
      s₀) x =
      rootPoint p₁ (Over.mk s₀) x * rootPoint p₂ (Over.mk s₀) y * rootPoint p₄ (Over.mk s₀) (-(-ε
          kH * x * y)) := by
    intro x y
    have h := congrArg (fun z => G.constantPoint Nc (Over.mk s₀) * z * (G.constantPoint Nc (Over.mk
        s₀))⁻¹) (h3' x y)
    simp only [conjm, cb2, cba, cb3] at h
    exact h
  -- the four identities of SGA 3, Exp. XXIII, 3.4.5–3.4.8
  have hI := g2_identity_I (fun t => rootPoint (v a) (Over.mk s₀) t) (fun t => rootPoint (v c)
      (Over.mk s₀) t)
    (fun t => rootPoint p₁ (Over.mk s₀) t) (fun t => rootPoint p₂ (Over.mk s₀) t) (fun t =>
        rootPoint p₃ (Over.mk s₀) (-t))
    (fun t => rootPoint p₄ (Over.mk s₀) (-t)) (fun t => rootPoint (v nc) (Over.mk s₀) t)
    (fun s t => rootPoint_add _ _ s t) hP3' hP4' (fun s t => rootPoint_add _ _ s t)
    (G.constantPoint Nc (Over.mk s₀)) hNcZ (ε k₀) (ε k₁) (-ε k₂) (-ε k₃) (ε l₀) (-ε l₁) (-ε l₂) (ε
        kJ)
    h1' h2' h4' cbb cba cb1 cb2 cb3 cb4 hnba hb1 hb2 hb4 hnb2 hnb3 h23 h24 h34
  have hII := g2_identity_II (fun t => rootPoint (v a) (Over.mk s₀) t) (fun t => rootPoint (v c)
      (Over.mk s₀) t)
    (fun t => rootPoint p₁ (Over.mk s₀) t) (fun t => rootPoint p₂ (Over.mk s₀) t) (fun t =>
        rootPoint p₃ (Over.mk s₀) (-t))
    (fun t => rootPoint p₄ (Over.mk s₀) (-t)) (fun t => rootPoint (v na) (Over.mk s₀) t)
    (fun s t => rootPoint_add _ _ s t) hP4' (fun s t => rootPoint_add _ _ s t)
    (G.constantPoint Na (Over.mk s₀)) hNaZ (ε k₀) (ε k₁) (-ε k₂) (-ε k₃) (-ε kH) (ε kJ)
    h1' h4' h6' caa cab ca1 ca2 ca3 ca4 hnab hb1 hb2 hb4 h13 h14 h23 h24
  have hIII := g2_identity_III (fun t => rootPoint (v c) (Over.mk s₀) t) (fun t => rootPoint p₃
      (Over.mk s₀) (-t))
    (fun t => rootPoint p₄ (Over.mk s₀) (-t)) (fun t => rootPoint (v nc) (Over.mk s₀) t) (fun s t
        => rootPoint_add _ _ s t)
    (G.constantPoint Nc (Over.mk s₀)) hNcZ (ε kJ) h4' cbb cb3 cb4 hnb3
  obtain ⟨W, hIV⟩ := g2_identity_IV (fun t => rootPoint (v a) (Over.mk s₀) t) (fun t => rootPoint
      (v c) (Over.mk s₀) t)
    (fun t => rootPoint p₁ (Over.mk s₀) t) (fun t => rootPoint p₂ (Over.mk s₀) t) (fun t =>
        rootPoint p₃ (Over.mk s₀) (-t))
    (fun t => rootPoint p₄ (Over.mk s₀) (-t)) (fun t => rootPoint (v na) (Over.mk s₀) t)
    (fun s t => rootPoint_add _ _ s t) (fun s t => rootPoint_add _ _ s t)
    (fun s t => rootPoint_add _ _ s t) (fun s t => rootPoint_add _ _ s t) hP4'
    (fun s t => rootPoint_add _ _ s t)
    (G.constantPoint Na (Over.mk s₀)) hNaZ (ε k₀) (ε k₁) (-ε k₂) (-ε k₃) (ε l₀) (-ε l₁) (-ε l₂) (-ε
        kH) (ε kJ)
    h1' h2' h3' h4' h6' caa cana cab ca1 ca2 ca3 ca4 hb1 hb2 hb4 h13 h14 h23 h24 h34
  -- comparison of coordinates in the big cell of `b`
  have nodupA : [a, d₁, d₂, d₃, d₄].Nodup := by
    simp [hd₁₂, hd₁₃, hd₁₄, hd₂₃, hd₂₄, hd₃₄, Ne.symm hd₁a, Ne.symm hd₂a, Ne.symm hd₃a,
      Ne.symm hd₄a]
  have nodupC : [c, d₁, d₂, d₃, d₄].Nodup := by
    simp [hd₁₂, hd₁₃, hd₁₄, hd₂₃, hd₂₄, hd₃₄, Ne.symm hd₁c, Ne.symm hd₂c, Ne.symm hd₃c,
      Ne.symm hd₄c]
  have posA : ∀ x ∈ [a, d₁, d₂, d₃, d₄], b.IsPos x := by
    simp [hapos, hd₁pos, hd₂pos, hd₃pos, hd₄pos]
  have posC : ∀ x ∈ [c, d₁, d₂, d₃, d₄], b.IsPos x := by
    simp [hcpos, hd₁pos, hd₂pos, hd₃pos, hd₄pos]
  have nodup34 : [d₃, d₄].Nodup := by simp [hd₃₄]
  have pos34 : ∀ x ∈ [d₃, d₄], b.IsPos x := by simp [hd₃pos, hd₄pos]
  rw [← hv'a, ← hv'd₁, ← hv'd₂, ← hv'd₃, ← hv'd₄] at hI
  obtain ⟨I0, -, I2, I3, I4⟩ := eq_of_prod_five hG hmax hP hv' b nodupA posA s₀ hI
  rw [← hv'c, ← hv'd₁, ← hv'd₂, ← hv'd₃, ← hv'd₄] at hII
  obtain ⟨II0, -, II2, -, -⟩ := eq_of_prod_five hG hmax hP hv' b nodupC posC s₀ hII
  have hIII' := hIII.trans (h34 _ _).symm
  rw [← hv'd₃, ← hv'd₄] at hIII'
  obtain ⟨III0, -⟩ := eq_of_prod_two hG hmax hP hv' b nodup34 pos34 s₀ hIII'
  have hIV' := hIV
  rw [← one_mul (rootPoint p₁ (Over.mk s₀) 1), ← rootPoint_zero (v c) (Over.mk s₀)] at hIV'
  rw [← hv'c, ← hv'd₁, ← hv'd₂, ← hv'd₃, ← hv'd₄] at hIV'
  obtain ⟨IV0, IV1, -, -, -⟩ := eq_of_prod_five hG hmax hP hv' b nodupC posC s₀ hIV'
  -- solving for the constants
  have ha₀ : ε k₀ = 1 := by linear_combination -I0
  have ha₂ : ε k₂ = -1 := by linear_combination II0
  have ha₁ : ε k₁ = 1 := by linear_combination II2 + ha₀
  have hJ : ε kJ = -1 := by linear_combination -III0
  rw [ha₀, ha₁] at I2
  have hE : ε l₀ = 2 := by linear_combination -I2
  rw [ha₁, hE] at IV1
  have hH : ε kH = -3 := by linear_combination IV1
  rw [ha₂, hH] at IV0
  have hF : ε l₁ = -3 := by linear_combination IV0
  rw [ha₀, ha₂, hF, hJ] at I3
  have ha₃ : ε k₃ = -1 := by linear_combination I3
  rw [ha₀, ha₂, ha₃, hJ] at I4
  have hG' : ε l₂ = -3 := by linear_combination -I4
  have h56 : rootPoint p₄ (Over.mk s₀) (ε k₅ * 1 * 1) = rootPoint p₄ (Over.mk s₀) (-(-ε kH * 1 *
      1)) :=
    mul_left_cancel ((F5 1 1).symm.trans (h6' 1 1))
  have h56' := congrArg (fun z => rootPoint p₃ (Over.mk s₀) 0 * z) h56
  rw [← hv'd₃, ← hv'd₄] at h56'
  obtain ⟨-, h5⟩ := eq_of_prod_two hG hmax hP hv' b nodup34 pos34 s₀ h56'
  have hk5 : ε k₅ = -3 := by linear_combination h5 + hH
  have hk₀ : k₀ = 1 := hεinj _ _ (by rw [map_one]; exact ha₀)
  have hk₁ : k₁ = 1 := hεinj _ _ (by rw [map_one]; exact ha₁)
  have hk₂ : k₂ = -1 := hεinj _ _ (by rw [map_neg, map_one]; exact ha₂)
  have hk₃ : k₃ = -1 := hεinj _ _ (by rw [map_neg, map_one]; exact ha₃)
  have hl₀ : l₀ = 2 := hεinj _ _ (by rw [map_ofNat]; exact hE)
  have hl₁ : l₁ = -3 := hεinj _ _ (by rw [map_neg, map_ofNat]; exact hF)
  have hl₂ : l₂ = -3 := hεinj _ _ (by rw [map_neg, map_ofNat]; exact hG')
  have hkH : kH = -3 := hεinj _ _ (by rw [map_neg, map_ofNat]; exact hH)
  have hkJ : kJ = -1 := hεinj _ _ (by rw [map_neg, map_one]; exact hJ)
  have hk₅ : k₅ = -3 := hεinj _ _ (by rw [map_neg, map_ofNat]; exact hk5)
  refine ⟨fun B _ s x y => ?_, fun B _ s x y => ?_, fun B _ s x y => ?_, fun B _ s x y => ?_,
    fun B _ s x y => ?_⟩
  · rw [hK₁ B s x y, hk₀, hk₁, hk₂, hk₃]
    simp only [map_one, map_neg, one_mul, neg_mul, mul_assoc]
  · rw [hK₂ B s x y, hl₀, hl₁, hl₂]
    simp only [map_ofNat, map_neg, neg_mul, mul_assoc]
  · rw [hkH' B s x y, hkH]
    simp only [map_ofNat, map_neg, neg_mul]
  · rw [hkJ' B s x y, hkJ]
    simp only [map_one, map_neg, one_mul, neg_mul]
  · rw [hK₅ B s x y, hk₅]
    simp only [map_ofNat, map_neg, neg_mul]

end TypeG2

end LocalSplitCell

open LocalSplitCell in
/-- **Commutators of type `G₂`.** For a reductive group scheme over a commutative ring with a
fibrewise maximal coordinate split torus `i`, a fibrewise root datum `P`, and root
parametrizations `v` of all roots, let `a` (short) and `c` (long) be simple roots of a base with
`⟨a, c^∨⟩ = -1` and `⟨c, a^∨⟩ = -3`, whose Weyl points `N_a`, `N_c` act by `s_a`, `s_c`.
Assume `N_a v_a(x) N_a⁻¹ = v_{-a}(-x)`, `N_c v_c(x) N_c⁻¹ = v_{-c}(-x)`, and that `N_a²`, `N_c²`
act on every root parametrization of a root `β` by `(-1)^⟨β, a^∨⟩`, `(-1)^⟨β, c^∨⟩`. With
`p₁ = Ad(N_c) ∘ v_a`, `p₂ = Ad(N_a) ∘ p₁`, `p₃ = Ad(N_a) ∘ v_c`, `p₄ = Ad(N_c) ∘ p₃` and
`[g, h] = (g h)⁻¹ (h g)`, over every ring over `R`:
`[v_a(x), v_c(y)] = p₁(x y) p₂(x² y) p₃(-x³ y) p₄(-x³ y²)`,
`[v_a(x), p₁(y)] = p₂(2 x y) p₃(-3 x² y) p₄(-3 x y²)`, `[v_a(x), p₂(y)] = p₃(-3 x y)`,
`[v_c(x), p₃(y)] = p₄(-x y)` and `[p₁(x), p₂(y)] = p₄(-3 x y)`. -/
def LocalSplitTypeG2CommutatorStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type u) [Fintype I] [DecidableEq I]
    (J : Type u) (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
    ∀ (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
    ∀ (v : J → (Ga R ⟶ G)), (∀ α, IsRootParametrization i (P.root α) (v α)) →
    ∀ (b : P.Base) (a c : J), a ∈ b.support → c ∈ b.support → a ≠ c →
    P.pairingIn ℤ a c = -1 →
    P.pairingIn ℤ c a = -3 →
    IsWeylPoint i (weylPoint (v a) (v (P.reflectionPerm a a))) (P.reflection a) →
    IsWeylPoint i (weylPoint (v c) (v (P.reflectionPerm c c))) (P.reflection c) →
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
        (x : Γ((Over.mk s).left, ⊤)),
        G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
            rootPoint (v a) (Over.mk s) x *
            (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s))⁻¹ =
          rootPoint (v (P.reflectionPerm a a)) (Over.mk s) (-x)) →
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
        (x : Γ((Over.mk s).left, ⊤)),
        G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s) *
            rootPoint (v c) (Over.mk s) x *
            (G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s))⁻¹ =
          rootPoint (v (P.reflectionPerm c c)) (Over.mk s) (-x)) →
    (∀ (β : J) (w : Ga R ⟶ G), IsRootParametrization i (P.root β) w →
        ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
        (x : Γ((Over.mk s).left, ⊤)),
        (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
            G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s)) *
            rootPoint w (Over.mk s) x *
            (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
              G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s))⁻¹ =
          rootPoint w (Over.mk s) ((P.pairingIn ℤ β a).negOnePow • x)) →
    (∀ (β : J) (w : Ga R ⟶ G), IsRootParametrization i (P.root β) w →
        ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
        (x : Γ((Over.mk s).left, ⊤)),
        (G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s) *
            G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s)) *
            rootPoint w (Over.mk s) x *
            (G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s) *
              G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s))⁻¹ =
          rootPoint w (Over.mk s) ((P.pairingIn ℤ β c).negOnePow • x)) →
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (x * y)) *
        rootPoint ((v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) ≫
            (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (x ^ 2 * y)) *
        rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(x ^ 3 * y))) *
        rootPoint ((v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) ≫
            (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(x ^ 3 * y ^ 2)))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk
              s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk
            s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint ((v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) ≫
          (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (2 * x * y)) *
        rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(3 * x ^ 2 * y))) *
        rootPoint ((v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) ≫
            (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(3 * x * y ^ 2)))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint ((v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) ≫
              (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
              ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint ((v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) ≫
            (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(3 * x * y)))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk
              s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk
            s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint ((v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) ≫
          (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(x * y)))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint ((v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) ≫
              (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
              ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint ((v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) ≫
            (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk
              s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint ((v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom) ≫
          (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(3 * x * y))))

open LocalSplitCell in
/-- The `G₂` commutator statement holds at full universe. -/
theorem localSplitTypeG2Commutator : LocalSplitTypeG2CommutatorStatement.{u} := by
  intro R _ I _ _ J G _ hG i hmax P hP v hv b a c ha hc hac h1 h2 hna hnc hROa hROc hsqa hsqc
  exact g2_constants hG hmax hP hv ha hc hac h1 h2 hna hnc hROa hROc hsqa hsqc

end Langlands.GroupScheme
