import Langlands.GroupScheme.Reductive.LocalSplitTypeA2
import Langlands.GroupScheme.Reductive.LocalRootParametrizationRigidity

/-! # The commutators of two simple root groups of type `B₂` -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.LinearAlgebra

section RankTwoB2

variable {I : Type*} {J : Type*} [Finite J] [DecidableEq J] {P : RootDatum J (I → ℤ) (I → ℤ)}
  [P.IsReduced] {b : P.Base} {a c : J}

/-- **Roots of type `B₂`, nonnegative coefficients.** If `a`, `c` are distinct simple roots
with `⟨a, c^∨⟩ = -1` and `⟨c, a^∨⟩ = -2` (so `a` is short), the roots `p • a + q • c` with
`p, q ≥ 0` are `a`, `c`, `a + c` and `2 a + c`. -/
theorem b2_coeffs_of_nonneg (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -2) :
    ∀ (n : ℕ) {α : J} {p q : ℤ}, p + q = n → 0 ≤ p → 0 ≤ q →
      P.root α = p • P.root a + q • P.root c →
      (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 1) ∨ (p = 2 ∧ q = 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α p q hn hp hq h
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
        rcases (show (p = 2 ∧ q = 1) ∨ (p = 3 ∧ q = 1) by omega) with hpq | hpq
        · exact Or.inr (Or.inr (Or.inr hpq))
        · exfalso
          have hmem : P.root c + (3 : ℕ) • P.root a ∈ Set.range P.root :=
            ⟨α, by rw [h, hpq.1, hpq.2]; module⟩
          rw [RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli] at hmem
          omega
      · have := ih (n - 1) (by omega) (p := p) (q := q - 1) (by omega) hp (by omega) h'
        rcases (show (p = 1 ∧ q = 2) ∨ (p = 2 ∧ q = 2) by omega) with hpq | hpq
        · exfalso
          have hmem : P.root a + (2 : ℕ) • P.root c ∈ Set.range P.root :=
            ⟨α, by rw [h, hpq.1, hpq.2]; simp [two_smul]⟩
          rw [RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli'] at hmem
          omega
        · exfalso
          -- `2 a + 2 c` is twice the root `a + c`
          have hs : P.root (P.reflectionPerm c a) = P.root a + P.root c := by
            have hp' : P.pairing a c = -1 := by
              rw [← P.algebraMap_pairingIn ℤ, h1]
              simp
            rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hp',
              neg_smul, one_smul, sub_neg_eq_add]
          exact P.nsmul_notMem_range_root (n := 2) (i := P.reflectionPerm c a)
            ⟨α, by rw [h, hpq.1, hpq.2, hs]; module⟩

/-- **Roots of type `B₂`, all signs.** -/
theorem b2_coeffs (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -2) {α : J} {p q : ℤ}
    (h : P.root α = p • P.root a + q • P.root c) :
    (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 1) ∨ (p = 2 ∧ q = 1) ∨
      (p = -1 ∧ q = 0) ∨ (p = 0 ∧ q = -1) ∨ (p = -1 ∧ q = -1) ∨ (p = -2 ∧ q = -1) := by
  rcases sign_of_root_eq_pair ha hc hac h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rcases b2_coeffs_of_nonneg ha hc hac h1 h2 (p + q).toNat (by omega) hp hq h with
      h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
  · have h' : P.root (P.reflectionPerm α α) = (-p) • P.root a + (-q) • P.root c := by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, h]
      simp only [neg_smul, neg_add]
    rcases b2_coeffs_of_nonneg ha hc hac h1 h2 (-p + -q).toNat (by omega) (by omega)
      (by omega) h' with h'' | h'' | h'' | h'' <;> omega

end RankTwoB2

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

namespace LocalSplitCell

section TypeB2Group

/-- **The `B₂` group computation**, in an abstract group (SGA 3, Exp. XXIII, 3.3.3–3.3.5).
`Pa`, `Pb`, `Pab`, `P2`, `Pna`, `Pnb` play the root groups of `a`, `c`, `a + c`, `2 a + c`,
`-a`, `-c`, and `Na`, `Nb` the Weyl points of `a` and `c`. From the commutation formulas
`(1)` and `(2)`, the conjugation actions of `Na` and `Nb`, and some commutations, the
definitions `Pab = Ad(Nb) Pa` and `P2 = Ad(Na) Pb` give two identities between products of
positive root group elements. -/
theorem b2_group_identities {Γ M : Type*} [CommRing Γ] [Group M]
    (Pa Pb Pab P2 Pna Pnb : Γ → M)
    (hPa : ∀ s t, Pa (s + t) = Pa s * Pa t) (hP2 : ∀ s t, P2 (s + t) = P2 s * P2 t)
    (hPnb : ∀ s t, Pnb (s + t) = Pnb s * Pnb t) (Na Nb : M) (hNa : Na = Pna (-1) * Pa 1 * Pna (-1)) (hNb : Nb = Pnb (-1) * Pb 1 * Pnb (-1))
    (A B C k : Γ)
    (h1 : ∀ x y, Pb y * Pa x = Pa x * Pb y * Pab (A * x * y) * P2 (B * x ^ 2 * y))
    (h2 : ∀ x y, Pab y * Pa x = Pa x * Pab y * P2 (C * x * y))
    (cbb : ∀ y, Nb * Pb y * Nb⁻¹ = Pnb (-y)) (cba : ∀ x, Nb * Pa x * Nb⁻¹ = Pab x)
    (cbab : ∀ t, Nb * Pab t * Nb⁻¹ = Pa (-t)) (cb2 : ∀ t, Nb * P2 t * Nb⁻¹ = P2 t)
    (cab : ∀ y, Na * Pb y * Na⁻¹ = P2 y) (caa : ∀ x, Na * Pa x * Na⁻¹ = Pna (-x))
    (caab : ∀ t, Na * Pab t * Na⁻¹ = Pab (k * t)) (ca2 : ∀ t, Na * P2 t * Na⁻¹ = Pb t)
    (hnab : ∀ x y, Pna x * Pb y = Pb y * Pna x) (hnba : ∀ x y, Pnb x * Pa y = Pa y * Pnb x)
    (hbab : ∀ x y, Pb x * Pab y = Pab y * Pb x) (hb2 : ∀ x y, Pb x * P2 y = P2 y * Pb x)
    (hnb2 : ∀ x y, Pnb x * P2 y = P2 y * Pnb x) :
    Pa 1 * Pab A * P2 B = Pa A * Pab 1 * P2 (C * A - B) ∧
      Pb 1 * Pab (-A) * P2 B = P2 1 * Pab (k * A) * Pb B := by
  have hPa0 : Pa 0 = 1 := by
    have h := hPa 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hPainv : ∀ s, Pa (-s) = (Pa s)⁻¹ := fun s =>
    eq_inv_of_mul_eq_one_left (by rw [← hPa, neg_add_cancel, hPa0])
  have hP20 : P2 0 = 1 := by
    have h := hP2 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hP2inv : ∀ s, P2 (-s) = (P2 s)⁻¹ := fun s =>
    eq_inv_of_mul_eq_one_left (by rw [← hP2, neg_add_cancel, hP20])
  have conj_mul : ∀ (N x y : M), N * (x * y) * N⁻¹ = (N * x * N⁻¹) * (N * y * N⁻¹) := by
    intro N x y
    group
  constructor
  · -- `Nb Pa(1) Nb⁻¹ = Pab 1`, expanded
    have hc : Pnb (-1) * Pa 1 * (Pnb (-1))⁻¹ = Pa 1 := by
      rw [hnba]
      group
    have key : Pab 1 = Pnb (-1) * (Pb 1 * (Pnb (-1) * Pa 1 * (Pnb (-1))⁻¹) * (Pb 1)⁻¹) *
        (Pnb (-1))⁻¹ := by
      rw [← cba 1, hNb]
      group
    rw [hc] at key
    have S1 : Pb 1 * Pa 1 * (Pb 1)⁻¹ = (Pnb (-1))⁻¹ * Pab 1 * Pnb (-1) := by
      rw [key]
      group
    -- the left side by `(1)`
    have h11 := h1 1 1
    simp only [mul_one, one_pow] at h11
    have S2 : Pb 1 * Pa 1 * (Pb 1)⁻¹ = Pa 1 * Pab A * P2 B := by
      rw [h11]
      calc Pa 1 * Pb 1 * Pab A * P2 B * (Pb 1)⁻¹
          = Pa 1 * (Pb 1 * Pab A) * P2 B * (Pb 1)⁻¹ := by group
        _ = Pa 1 * (Pab A * Pb 1) * P2 B * (Pb 1)⁻¹ := by rw [hbab]
        _ = Pa 1 * Pab A * (Pb 1 * P2 B) * (Pb 1)⁻¹ := by group
        _ = Pa 1 * Pab A * (P2 B * Pb 1) * (Pb 1)⁻¹ := by rw [hb2]
        _ = Pa 1 * Pab A * P2 B := by group
    -- the right side by `(5)`, the conjugate of `(1)` by `Nb`, at `y = -1`
    have hPnb0 : Pnb 0 = 1 := by
      have h := hPnb 0 0
      rw [add_zero] at h
      exact mul_eq_left.mp h.symm
    have hPnbinv : (Pnb (-1))⁻¹ = Pnb 1 :=
      (eq_inv_of_mul_eq_one_left (by rw [← hPnb, add_neg_cancel, hPnb0])).symm
    have h5 := congrArg (fun z => Nb * z * Nb⁻¹) (h1 1 (-1))
    simp only [conj_mul, cbb, cba, cbab, cb2, mul_one, one_pow, mul_neg, neg_neg] at h5
    have S3 : (Pnb (-1))⁻¹ * Pab 1 * Pnb (-1) = Pab 1 * Pa A * P2 (-B) := by
      rw [hPnbinv, show Pnb (-1) = (Pnb 1)⁻¹ by rw [← hPnbinv, inv_inv]]
      calc Pnb 1 * Pab 1 * (Pnb 1)⁻¹
          = (Pnb 1 * Pab 1) * (Pnb 1)⁻¹ := rfl
        _ = Pab 1 * Pnb 1 * Pa A * P2 (-B) * (Pnb 1)⁻¹ := by rw [h5]
        _ = Pab 1 * (Pnb 1 * Pa A) * P2 (-B) * (Pnb 1)⁻¹ := by group
        _ = Pab 1 * (Pa A * Pnb 1) * P2 (-B) * (Pnb 1)⁻¹ := by rw [hnba]
        _ = Pab 1 * Pa A * (Pnb 1 * P2 (-B)) * (Pnb 1)⁻¹ := by group
        _ = Pab 1 * Pa A * (P2 (-B) * Pnb 1) * (Pnb 1)⁻¹ := by rw [hnb2]
        _ = Pab 1 * Pa A * P2 (-B) := by group
    have S4 : Pab 1 * Pa A = Pa A * Pab 1 * P2 (C * A) := by
      have := h2 A 1
      rw [mul_one] at this
      exact this
    rw [← S2, S1, S3, S4, mul_assoc, ← hP2, sub_eq_add_neg]
  · -- `Na Pb(1) Na⁻¹ = P2 1`, expanded
    have hc : Pna (-1) * Pb 1 * (Pna (-1))⁻¹ = Pb 1 := by
      rw [hnab]
      group
    have key : P2 1 = Pna (-1) * (Pa 1 * (Pna (-1) * Pb 1 * (Pna (-1))⁻¹) * (Pa 1)⁻¹) *
        (Pna (-1))⁻¹ := by
      rw [← cab 1, hNa]
      group
    rw [hc] at key
    have T1 : Pa 1 * Pb 1 * (Pa 1)⁻¹ = (Pna (-1))⁻¹ * P2 1 * Pna (-1) := by
      rw [key]
      group
    -- the left side by `(1)` at `x = -1`
    have h1m := h1 (-1) 1
    simp only [mul_one, neg_one_sq, mul_neg] at h1m
    have T2 : Pa 1 * Pb 1 * (Pa 1)⁻¹ = Pb 1 * Pab (-A) * P2 B := by
      rw [hPainv] at h1m
      calc Pa 1 * Pb 1 * (Pa 1)⁻¹ = Pa 1 * (Pb 1 * (Pa 1)⁻¹) := by group
        _ = Pa 1 * ((Pa 1)⁻¹ * Pb 1 * Pab (-A) * P2 B) := by rw [h1m]
        _ = Pb 1 * Pab (-A) * P2 B := by group
    -- the right side by `(3)`, the conjugate of `(1)` by `Na`
    have h3 := congrArg (fun z => Na * z * Na⁻¹) (h1 1 1)
    simp only [conj_mul, cab, caa, caab, ca2, mul_one, one_pow] at h3
    have T3 : (Pna (-1))⁻¹ * P2 1 * Pna (-1) = P2 1 * Pab (k * A) * Pb B := by
      calc (Pna (-1))⁻¹ * P2 1 * Pna (-1) = (Pna (-1))⁻¹ * (P2 1 * Pna (-1)) := by group
        _ = (Pna (-1))⁻¹ * (Pna (-1) * P2 1 * Pab (k * A) * Pb B) := by rw [h3]
        _ = P2 1 * Pab (k * A) * Pb B := by group
    rw [← T2, T1, T3]

/-- Solving a product identity `Pa x₁ Pab y₁ P2 z₁ = Pa x₂ Pab y₂ P2 z₂` for the first factor,
when `Pab` and `P2` commute. -/
theorem solve_mul_three {Γ M : Type*} [CommRing Γ] [Group M] (X Y Z : Γ → M)
    (hX : ∀ s t, X (s + t) = X s * X t) (hY : ∀ s t, Y (s + t) = Y s * Y t)
    (hZ : ∀ s t, Z (s + t) = Z s * Z t) (hYZ : ∀ s t, Y s * Z t = Z t * Y s)
    {x₁ y₁ z₁ x₂ y₂ z₂ : Γ} (h : X x₁ * Y y₁ * Z z₁ = X x₂ * Y y₂ * Z z₂) :
    X (x₁ - x₂) = Y (y₂ - y₁) * Z (z₂ - z₁) := by
  have inv_of : ∀ (W : Γ → M), (∀ s t, W (s + t) = W s * W t) → ∀ s, W (-s) = (W s)⁻¹ := by
    intro W hW s
    have h0 : W 0 = 1 := by
      have h' := hW 0 0
      rw [add_zero] at h'
      exact mul_eq_left.mp h'.symm
    exact eq_inv_of_mul_eq_one_left (by rw [← hW, neg_add_cancel, h0])
  have hx : X x₁ = X x₂ * Y y₂ * Z z₂ * (Z z₁)⁻¹ * (Y y₁)⁻¹ := by
    rw [← h]
    group
  rw [sub_eq_add_neg, add_comm, hX, hx, sub_eq_add_neg, sub_eq_add_neg, hY, hZ, inv_of X hX,
    inv_of Y hY, inv_of Z hZ]
  calc (X x₂)⁻¹ * (X x₂ * Y y₂ * Z z₂ * (Z z₁)⁻¹ * (Y y₁)⁻¹)
      = Y y₂ * (Z z₂ * (Z z₁)⁻¹ * (Y y₁)⁻¹) := by group
    _ = Y y₂ * (Z (z₂ + -z₁) * Y (-y₁)) := by rw [hZ, inv_of Z hZ, inv_of Y hY]
    _ = Y y₂ * (Y (-y₁) * Z (z₂ + -z₁)) := by rw [hYZ]
    _ = Y y₂ * (Y y₁)⁻¹ * (Z z₂ * (Z z₁)⁻¹) := by rw [hZ, inv_of Z hZ, inv_of Y hY]; group

end TypeB2Group

section TypeB2

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {v : J → (Ga R ⟶ G)}

/-- **The `B₂` commutator constants.** Let `a` (short) and `c` (long) be simple roots of a base
with `⟨a, c^∨⟩ = -1` and `⟨c, a^∨⟩ = -2`, and let `v` be root parametrizations of all roots
whose points `N_a = v_{-a}(-1) v_a(1) v_{-a}(-1)` and `N_c` are Weyl points acting by `s_a`
and `s_c`. Assume the rank-one identities `N_a v_a(x) N_a⁻¹ = v_{-a}(-x)`,
`N_c v_c(x) N_c⁻¹ = v_{-c}(-x)`, and that `N_a²` fixes `v_c` while `N_c²` acts on `v_a` by
`x ↦ -x`. Put `p₁ = Ad(N_c) ∘ v_a` (root `a + c`) and `p₂ = Ad(N_a) ∘ v_c` (root `2 a + c`).
Then `(v_a(x) v_c(y))⁻¹ (v_c(y) v_a(x)) = p₁(x y) p₂(x² y)`,
`(v_a(x) p₁(y))⁻¹ (p₁(y) v_a(x)) = p₂(2 x y)`, and `N_a p₁(x) N_a⁻¹ = p₁(-x)`. -/
theorem b2_constants [IsLocalRing R] (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    {b : P.Base} {a c : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -2)
    (hna : IsWeylPoint i (weylPoint (v a) (v (P.reflectionPerm a a))) (P.reflection a))
    (hnc : IsWeylPoint i (weylPoint (v c) (v (P.reflectionPerm c c))) (P.reflection c))
    (hROa : ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)),
      G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
          rootPoint (v a) (Over.mk s) x *
          (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s))⁻¹ =
        rootPoint (v (P.reflectionPerm a a)) (Over.mk s) (-x))
    (hROc : ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)),
      G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s) *
          rootPoint (v c) (Over.mk s) x *
          (G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s))⁻¹ =
        rootPoint (v (P.reflectionPerm c c)) (Over.mk s) (-x))
    (hsqa : ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)),
      (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
          G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s)) *
          rootPoint (v c) (Over.mk s) x *
          (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
            G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s))⁻¹ =
        rootPoint (v c) (Over.mk s) x)
    (hsqc : ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)),
      (G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s) *
          G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s)) *
          rootPoint (v a) (Over.mk s) x *
          (G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s) *
            G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s))⁻¹ =
        rootPoint (v a) (Over.mk s) (-x)) :
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom)
          (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (x * y)) *
        rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom)
          (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (x ^ 2 * y))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom)
            (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom)
            (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom)
        (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (2 * x * y))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)),
      G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
          rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom)
            (Over.mk s) x *
          (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s))⁻¹ =
        rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom)
          (Over.mk s) (-x)) := by
  classical
  have := hP.finite
  have : P.IsReduced := hP.isReduced
  set na := P.reflectionPerm a a with hna_def
  set nc := P.reflectionPerm c c with hnc_def
  set Na := weylPoint (v a) (v na) with hNa_def
  set Nc := weylPoint (v c) (v nc) with hNc_def
  set p₁ := v a ≫ (G.innerIso Nc).hom with hp₁_def
  set p₂ := v c ≫ (G.innerIso Na).hom with hp₂_def
  set d₁ := P.reflectionPerm c a with hd₁_def
  set d₂ := P.reflectionPerm a c with hd₂_def
  have hpac : P.pairing a c = -1 := by
    rw [← P.algebraMap_pairingIn ℤ, h1]
    simp
  have hpca : P.pairing c a = -2 := by
    rw [← P.algebraMap_pairingIn ℤ, h2]
    simp
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
  have rd₂ : P.root d₂ = (2 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [hd₂_def, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hpca]
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
  have hcoeff := fun {α : J} {p q : ℤ} (h : P.root α = p • P.root a + q • P.root c) =>
    Langlands.LinearAlgebra.b2_coeffs ha hc hac h1 h2 h
  have cone_gen : ∀ {x y : J} {p q p' q' : ℤ}, P.root x = p • P.root a + q • P.root c →
      P.root y = p' • P.root a + q' • P.root c → ∀ (α : J) (dS dT : ℕ),
      (dS : ℤ) • P.root x + (dT : ℤ) • P.root y = P.root α →
      let P' := (dS : ℤ) * p + (dT : ℤ) * p'
      let Q' := (dS : ℤ) * q + (dT : ℤ) * q'
      (P' = 1 ∧ Q' = 0) ∨ (P' = 0 ∧ Q' = 1) ∨ (P' = 1 ∧ Q' = 1) ∨ (P' = 2 ∧ Q' = 1) ∨
        (P' = -1 ∧ Q' = 0) ∨ (P' = 0 ∧ Q' = -1) ∨ (P' = -1 ∧ Q' = -1) ∨
        (P' = -2 ∧ Q' = -1) := by
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
  have hd₁a : d₁ ≠ a := hdist rd₁ ra (by omega)
  have hd₁c : d₁ ≠ c := hdist rd₁ rc (by omega)
  have hd₁na : d₁ ≠ na := hdist rd₁ rna (by omega)
  have hd₁nc : d₁ ≠ nc := hdist rd₁ rnc (by omega)
  have hd₂a : d₂ ≠ a := hdist rd₂ ra (by omega)
  have hd₂c : d₂ ≠ c := hdist rd₂ rc (by omega)
  have hd₂na : d₂ ≠ na := hdist rd₂ rna (by omega)
  have hd₂nc : d₂ ≠ nc := hdist rd₂ rnc (by omega)
  -- the two conjugated parametrizations
  have hp₁ : IsRootParametrization i (P.root d₁) p₁ := by
    have h := (hv a).comp_innerIso hnc
    rw [hd₁_def, RootPairing.root_reflectionPerm]
    exact h
  have hp₂ : IsRootParametrization i (P.root d₂) p₂ := by
    have h := (hv c).comp_innerIso hna
    rw [hd₂_def, RootPairing.root_reflectionPerm]
    exact h
  let v' : J → (Ga R ⟶ G) := Function.update (Function.update v d₁ p₁) d₂ p₂
  have hv'd₂ : v' d₂ = p₂ := Function.update_self _ _ _
  have hv'd₁ : v' d₁ = p₁ := by
    rw [show v' d₁ = Function.update v d₁ p₁ d₁ from Function.update_of_ne hd₁₂ _ _]
    exact Function.update_self _ _ _
  have hv'o : ∀ x, x ≠ d₁ → x ≠ d₂ → v' x = v x := by
    intro x h₁ h₂
    rw [show v' x = Function.update v d₁ p₁ x from Function.update_of_ne h₂ _ _]
    exact Function.update_of_ne h₁ _ _
  have hv'a : v' a = v a := hv'o a (Ne.symm hd₁a) (Ne.symm hd₂a)
  have hv'c : v' c = v c := hv'o c (Ne.symm hd₁c) (Ne.symm hd₂c)
  have hv'na : v' na = v na := hv'o na (Ne.symm hd₁na) (Ne.symm hd₂na)
  have hv'nc : v' nc = v nc := hv'o nc (Ne.symm hd₁nc) (Ne.symm hd₂nc)
  have hv' : ∀ α, IsRootParametrization i (P.root α) (v' α) := by
    intro α
    by_cases h₂ : α = d₂
    · subst h₂
      rw [hv'd₂]
      exact hp₂
    · by_cases h₁ : α = d₁
      · subst h₁
        rw [hv'd₁]
        exact hp₁
      · rw [hv'o α h₁ h₂]
        exact hv α
  -- commutations
  have comm_of : ∀ {x y : J} {p q p' q' : ℤ} (hx : P.root x = p • P.root a + q • P.root c)
      (hy : P.root y = p' • P.root a + q' • P.root c), (p + p' ≠ 0 ∨ q + q' ≠ 0) →
      (∀ dS dT : ℤ, 1 ≤ dS → 1 ≤ dT →
        let P' := dS * p + dT * p'
        let Q' := dS * q + dT * q'
        ¬ ((P' = 1 ∧ Q' = 0) ∨ (P' = 0 ∧ Q' = 1) ∨ (P' = 1 ∧ Q' = 1) ∨ (P' = 2 ∧ Q' = 1) ∨
          (P' = -1 ∧ Q' = 0) ∨ (P' = 0 ∧ Q' = -1) ∨ (P' = -1 ∧ Q' = -1) ∨
          (P' = -2 ∧ Q' = -1))) →
      ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
        (z w : Γ((Over.mk s).left, ⊤)),
        rootPoint (v' x) (Over.mk s) z * rootPoint (v' y) (Over.mk s) w =
          rootPoint (v' y) (Over.mk s) w * rootPoint (v' x) (Over.mk s) z := by
    intro x y p q p' q' hx hy hne hcone B _ s z w
    refine rootPoint_commute_of_forall_ne hG hmax hP hv' (noopp hx hy hne) ?_ s z w
    intro α dS dT hS hT h
    exact hcone dS dT (by exact_mod_cast hS) (by exact_mod_cast hT) (cone_gen hx hy α dS dT h)
  have cm_na_c := comm_of rna rc (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_nc_a := comm_of rnc ra (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_c_d₁ := comm_of rc rd₁ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_c_d₂ := comm_of rc rd₂ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_nc_d₂ := comm_of rnc rd₂ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  have cm_d₁_d₂ := comm_of rd₁ rd₂ (by omega) (by intro dS dT h₁ h₂; simp only; omega)
  -- the commutator constants
  have hd₁' : P.root d₁ = P.root a + P.root c := by rw [rd₁, one_smul, one_smul]
  have hd₂' : P.root d₂ = (2 : ℤ) • P.root a + P.root c := by rw [rd₂, one_smul]
  have hd₂'' : P.root d₂ = P.root a + P.root d₁ := by rw [rd₂, rd₁]; module
  obtain ⟨A, B', hAB⟩ := exists_rootPoint_comm_two hG hmax hP hv' (β := a) (ε := c)
    (δ₁ := d₁) (δ₂ := d₂) (noopp ra rc (by omega)) hd₁' hd₂'
    (by
      intro α dS dT hS hT h
      have := cone_gen ra rc α dS dT h
      simp only at this
      omega)
    (fun s z w => cm_d₁_d₂ _ s z w)
  obtain ⟨C, hC⟩ := exists_rootPoint_comm_single hG hmax hP hv' (β := a) (ε := d₁) (δ := d₂)
    (noopp ra rd₁ (by omega)) hd₂''
    (by
      intro α dS dT hS hT h
      have := cone_gen ra rd₁ α dS dT h
      simp only at this
      omega)
  rw [hv'a, hv'c, hv'd₁, hv'd₂] at hAB
  rw [hv'a, hv'd₁, hv'd₂] at hC
  -- the unit `k` of `Ad(N_a)` on the root group of `a + c`
  have hpd₁a : P.pairing d₁ a = 0 := by
    rw [← RootPairing.root_coroot_eq_pairing, hd₁', map_add, LinearMap.add_apply,
      RootPairing.root_coroot_eq_pairing, RootPairing.root_coroot_eq_pairing,
      RootPairing.pairing_same, hpca]
    norm_num
  have hkp : IsRootParametrization i (P.root d₁) (p₁ ≫ (G.innerIso Na).hom) := by
    have h := hp₁.comp_innerIso hna
    have e : P.reflection a (P.root d₁) = P.root d₁ := by
      rw [RootPairing.reflection_apply_root, hpd₁a, zero_smul, sub_zero]
    rw [← e]
    exact h
  set κ := hkp.comparisonUnit hP d₁ hp₁ with hκ_def
  have hκ : p₁ ≫ (G.innerIso Na).hom = scaleHom (κ : R) ≫ p₁ :=
    hkp.comparisonUnit_spec hP d₁ hp₁
  have hconjk : ∀ (Z : Over (Spec (CommRingCat.of R))) (t : Γ(Z.left, ⊤)),
      G.constantPoint Na Z * rootPoint p₁ Z t * (G.constantPoint Na Z)⁻¹ =
        rootPoint p₁ Z (baseScalar Z (κ : R) * t) := by
    intro Z t
    rw [← GroupScheme.comp_innerIso_hom, ← rootPoint_comp, hκ, rootPoint_scaleHom]
  -- the definitions of `p₁` and `p₂` as conjugates
  have hdef₁ : ∀ (Z : Over (Spec (CommRingCat.of R))) (t : Γ(Z.left, ⊤)),
      rootPoint p₁ Z t = G.constantPoint Nc Z * rootPoint (v a) Z t * (G.constantPoint Nc Z)⁻¹ := by
    intro Z t
    rw [hp₁_def, rootPoint_comp, GroupScheme.comp_innerIso_hom]
  have hdef₂ : ∀ (Z : Over (Spec (CommRingCat.of R))) (t : Γ(Z.left, ⊤)),
      rootPoint p₂ Z t = G.constantPoint Na Z * rootPoint (v c) Z t * (G.constantPoint Na Z)⁻¹ := by
    intro Z t
    rw [hp₂_def, rootPoint_comp, GroupScheme.comp_innerIso_hom]
  -- the commutations in terms of `v`, `p₁`, `p₂`
  have cr_na_c : ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ _) z w,
      rootPoint (v na) (Over.mk s) z * rootPoint (v c) (Over.mk s) w =
        rootPoint (v c) (Over.mk s) w * rootPoint (v na) (Over.mk s) z := by
    intro B _ s z w
    have h := cm_na_c B s z w
    rwa [hv'na, hv'c] at h
  have cr_nc_a : ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ _) z w,
      rootPoint (v nc) (Over.mk s) z * rootPoint (v a) (Over.mk s) w =
        rootPoint (v a) (Over.mk s) w * rootPoint (v nc) (Over.mk s) z := by
    intro B _ s z w
    have h := cm_nc_a B s z w
    rwa [hv'nc, hv'a] at h
  have cr_c_d₁ : ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ _) z w,
      rootPoint (v c) (Over.mk s) z * rootPoint p₁ (Over.mk s) w =
        rootPoint p₁ (Over.mk s) w * rootPoint (v c) (Over.mk s) z := by
    intro B _ s z w
    have h := cm_c_d₁ B s z w
    rwa [hv'c, hv'd₁] at h
  have cr_c_d₂ : ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ _) z w,
      rootPoint (v c) (Over.mk s) z * rootPoint p₂ (Over.mk s) w =
        rootPoint p₂ (Over.mk s) w * rootPoint (v c) (Over.mk s) z := by
    intro B _ s z w
    have h := cm_c_d₂ B s z w
    rwa [hv'c, hv'd₂] at h
  have cr_nc_d₂ : ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ _) z w,
      rootPoint (v nc) (Over.mk s) z * rootPoint p₂ (Over.mk s) w =
        rootPoint p₂ (Over.mk s) w * rootPoint (v nc) (Over.mk s) z := by
    intro B _ s z w
    have h := cm_nc_d₂ B s z w
    rwa [hv'nc, hv'd₂] at h
  have cr_d₁_d₂ : ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ _) z w,
      rootPoint p₁ (Over.mk s) z * rootPoint p₂ (Over.mk s) w =
        rootPoint p₂ (Over.mk s) w * rootPoint p₁ (Over.mk s) z := by
    intro B _ s z w
    have h := cm_d₁_d₂ B s z w
    rwa [hv'd₁, hv'd₂] at h
  -- evaluation over `R` itself
  set s₀ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R) := 𝟙 _ with hs₀
  set e₀ := (Scheme.ΓSpecIso (CommRingCat.of R)).inv with he₀
  have hpre : ∀ r : R, (Spec.preimage s₀).hom r = r := by
    intro r
    rw [hs₀, Spec.preimage_id]
    rfl
  have hsurj : ∀ t : Γ((Over.mk s₀).left, ⊤), ∃ r : R, e₀ r = t :=
    fun t => ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom t, Iso.hom_inv_id_apply _ _⟩
  have hNaZ : G.constantPoint Na (Over.mk s₀) = rootPoint (v na) (Over.mk s₀) (-1) *
      rootPoint (v a) (Over.mk s₀) 1 * rootPoint (v na) (Over.mk s₀) (-1) := by
    rw [hNa_def]
    exact constantPoint_weylPoint _ _ _
  have hNcZ : G.constantPoint Nc (Over.mk s₀) = rootPoint (v nc) (Over.mk s₀) (-1) *
      rootPoint (v c) (Over.mk s₀) 1 * rootPoint (v nc) (Over.mk s₀) (-1) := by
    rw [hNc_def]
    exact constantPoint_weylPoint _ _ _
  obtain ⟨hI, hII⟩ := b2_group_identities (fun t => rootPoint (v a) (Over.mk s₀) t)
    (fun t => rootPoint (v c) (Over.mk s₀) t) (fun t => rootPoint p₁ (Over.mk s₀) t)
    (fun t => rootPoint p₂ (Over.mk s₀) t) (fun t => rootPoint (v na) (Over.mk s₀) t)
    (fun t => rootPoint (v nc) (Over.mk s₀) t)
    (fun s t => rootPoint_add _ _ s t) (fun s t => rootPoint_add _ _ s t)
    (fun s t => rootPoint_add _ _ s t)
    (G.constantPoint Na (Over.mk s₀)) (G.constantPoint Nc (Over.mk s₀)) hNaZ hNcZ
    (e₀ A) (e₀ B') (e₀ C) (baseScalar (Over.mk s₀) (κ : R))
    (by
      intro x y
      obtain ⟨x₀, rfl⟩ := hsurj x
      obtain ⟨y₀, rfl⟩ := hsurj y
      have h := hAB R s₀ x₀ y₀
      rw [hpre, hpre, map_mul, map_mul, map_mul, map_mul, map_pow,
        inv_mul_eq_iff_eq_mul] at h
      simp only
      rw [h]
      simp only [mul_assoc]
      rfl)
    (by
      intro x y
      obtain ⟨x₀, rfl⟩ := hsurj x
      obtain ⟨y₀, rfl⟩ := hsurj y
      have h := hC R s₀ x₀ y₀
      rw [hpre, map_mul, map_mul, inv_mul_eq_iff_eq_mul] at h
      simp only
      rw [h])
    (fun y => hROc R s₀ y) (fun x => (hdef₁ _ x).symm)
    (by
      intro t
      rw [hdef₁, ← hsqc R s₀ t]
      group)
    (by
      intro t
      have hcm : Commute (G.constantPoint Nc (Over.mk s₀)) (rootPoint p₂ (Over.mk s₀) t) := by
        rw [hNcZ]
        refine ((Commute.mul_left ?_ ?_).mul_left ?_)
        · exact cr_nc_d₂ R s₀ _ _
        · exact cr_c_d₂ R s₀ _ _
        · exact cr_nc_d₂ R s₀ _ _
      rw [hcm.eq, mul_inv_cancel_right])
    (fun y => (hdef₂ _ y).symm) (fun x => hROa R s₀ x) (fun t => hconjk _ t)
    (by
      intro t
      rw [hdef₂]
      calc G.constantPoint Na (Over.mk s₀) * (G.constantPoint Na (Over.mk s₀) *
            rootPoint (v c) (Over.mk s₀) t * (G.constantPoint Na (Over.mk s₀))⁻¹) *
            (G.constantPoint Na (Over.mk s₀))⁻¹
          = (G.constantPoint Na (Over.mk s₀) * G.constantPoint Na (Over.mk s₀)) *
            rootPoint (v c) (Over.mk s₀) t *
            (G.constantPoint Na (Over.mk s₀) * G.constantPoint Na (Over.mk s₀))⁻¹ := by group
        _ = rootPoint (v c) (Over.mk s₀) t := hsqa R s₀ t)
    (fun x y => cr_na_c R s₀ x y) (fun x y => cr_nc_a R s₀ x y)
    (fun x y => cr_c_d₁ R s₀ x y) (fun x y => cr_c_d₂ R s₀ x y)
    (fun x y => cr_nc_d₂ R s₀ x y)
  -- uniqueness of coordinates
  have hapos : b.IsPos a := b.isPos_of_mem_support ha
  have hcpos : b.IsPos c := b.isPos_of_mem_support hc
  have hd₁pos : b.IsPos d₁ := hapos.add hcpos hd₁'
  have hd₂pos : b.IsPos d₂ := hapos.add hd₁pos hd₂''
  have hsolI := solve_mul_three (fun t => rootPoint (v a) (Over.mk s₀) t)
    (fun t => rootPoint p₁ (Over.mk s₀) t) (fun t => rootPoint p₂ (Over.mk s₀) t)
    (fun s t => rootPoint_add _ _ s t) (fun s t => rootPoint_add _ _ s t)
    (fun s t => rootPoint_add _ _ s t) (fun s t => cr_d₁_d₂ R s₀ s t) hI
  simp only at hsolI
  have hII' := hII
  conv at hII' =>
    rhs
    rw [mul_assoc, ← cr_c_d₁ R s₀, ← mul_assoc, ← cr_c_d₂ R s₀, mul_assoc, ← cr_d₁_d₂ R s₀,
      ← mul_assoc]
  have hsolII := solve_mul_three (fun t => rootPoint (v c) (Over.mk s₀) t)
    (fun t => rootPoint p₁ (Over.mk s₀) t) (fun t => rootPoint p₂ (Over.mk s₀) t)
    (fun s t => rootPoint_add _ _ s t) (fun s t => rootPoint_add _ _ s t)
    (fun s t => rootPoint_add _ _ s t) (fun s t => cr_d₁_d₂ R s₀ s t) hII'
  simp only at hsolII
  have hcv' : ∀ z w : Γ((Over.mk s₀).left, ⊤),
      rootPoint (v' d₁) (Over.mk s₀) z * rootPoint (v' d₂) (Over.mk s₀) w =
        rootPoint (v' d₂) (Over.mk s₀) w * rootPoint (v' d₁) (Over.mk s₀) z :=
    fun z w => cm_d₁_d₂ R s₀ z w
  obtain ⟨z1, -, z3⟩ := coord_zero_of_eq_mul hG hmax hP hv' b hapos hd₁pos hd₂pos
    (Ne.symm hd₁a) (Ne.symm hd₂a) hd₁₂ s₀ hcv' _ _ _ (by rw [hv'a, hv'd₁, hv'd₂]; exact hsolI)
  obtain ⟨z4, z5, -⟩ := coord_zero_of_eq_mul hG hmax hP hv' b hcpos hd₁pos hd₂pos
    (Ne.symm hd₁c) (Ne.symm hd₂c) hd₁₂ s₀ hcv' _ _ _ (by rw [hv'c, hv'd₁, hv'd₂]; exact hsolII)
  have hinj : ∀ r : R, e₀ r = 0 → r = 0 := by
    intro r hr
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom hr
    rwa [he₀, Iso.inv_hom_id_apply, map_zero] at this
  have hbs : baseScalar (Over.mk s₀) (κ : R) = e₀ (κ : R) := rfl
  have hA1 : A = 1 := by
    have := hinj (1 - A) (by rw [map_sub, map_one]; exact z1)
    linear_combination -this
  have hB1 : B' = 1 := by
    have := hinj (1 - B') (by rw [map_sub, map_one]; exact z4)
    linear_combination -this
  have hC2 : C = 2 := by
    have := hinj (C * A - B' - B') (by rw [map_sub, map_sub, map_mul]; exact z3)
    rw [hA1, hB1] at this
    linear_combination this
  have hκ1 : (κ : R) = -1 := by
    have := hinj ((κ : R) * A - -A) (by rw [map_sub, map_neg, map_mul, ← hbs]; exact z5)
    rw [hA1] at this
    linear_combination this
  refine ⟨fun B _ s x y => ?_, fun B _ s x y => ?_, fun B _ s x => ?_⟩
  · rw [hAB B s x y, hA1, hB1, map_one, one_mul, one_mul]
  · rw [hC B s x y, hC2, map_ofNat]
  · rw [hconjk (Over.mk s) x, hκ1, map_neg, map_one, neg_one_mul]

end TypeB2

end LocalSplitCell

open LocalSplitCell in
/-- **Commutators of type `B₂`.** For a reductive group scheme over a commutative local ring with
a fibrewise maximal coordinate split torus `i`, a fibrewise root datum `P`, and root
parametrizations `v` of all roots, let `a` (short) and `c` (long) be simple roots of a base
with `⟨a, c^∨⟩ = -1` and `⟨c, a^∨⟩ = -2`, whose Weyl points `N_a`, `N_c` act by `s_a`, `s_c`.
Assume `N_a v_a(x) N_a⁻¹ = v_{-a}(-x)`, `N_c v_c(x) N_c⁻¹ = v_{-c}(-x)`, that `N_a²` fixes the
points of `v_c` and that `N_c²` acts on `v_a` by `x ↦ -x`. With `p₁ = Ad(N_c) ∘ v_a` and
`p₂ = Ad(N_a) ∘ v_c`, over every ring over `R`:
`(v_a(x) v_c(y))⁻¹ (v_c(y) v_a(x)) = p₁(x y) p₂(x² y)`,
`(v_a(x) p₁(y))⁻¹ (p₁(y) v_a(x)) = p₂(2 x y)`, and `N_a p₁(x) N_a⁻¹ = p₁(-x)`. -/
def LocalSplitTypeB2CommutatorStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I] [DecidableEq I]
    (J : Type u) (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
    ∀ (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
    ∀ (v : J → (Ga R ⟶ G)), (∀ α, IsRootParametrization i (P.root α) (v α)) →
    ∀ (b : P.Base) (a c : J), a ∈ b.support → c ∈ b.support → a ≠ c →
    P.pairingIn ℤ a c = -1 →
    P.pairingIn ℤ c a = -2 →
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
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
        (x : Γ((Over.mk s).left, ⊤)),
        (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
            G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s)) *
            rootPoint (v c) (Over.mk s) x *
            (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
              G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s))⁻¹ =
          rootPoint (v c) (Over.mk s) x) →
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
        (x : Γ((Over.mk s).left, ⊤)),
        (G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s) *
            G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s)) *
            rootPoint (v a) (Over.mk s) x *
            (G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s) *
              G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s))⁻¹ =
          rootPoint (v a) (Over.mk s) (-x)) →
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom)
          (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (x * y)) *
        rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom)
          (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (x ^ 2 * y))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom)
            (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom)
            (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom)
        (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (2 * x * y))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)),
      G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s) *
          rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom)
            (Over.mk s) x *
          (G.constantPoint (weylPoint (v a) (v (P.reflectionPerm a a))) (Over.mk s))⁻¹ =
        rootPoint (v a ≫ (G.innerIso (weylPoint (v c) (v (P.reflectionPerm c c)))).hom)
          (Over.mk s) (-x))

open LocalSplitCell in
/-- The `B₂` commutator statement holds at full universe. -/
theorem localSplitTypeB2Commutator : LocalSplitTypeB2CommutatorStatement.{u} := by
  intro R _ _ I _ _ J G _ hG i hmax P hP v hv b a c ha hc hac h1 h2 hna hnc hROa hROc hsqa hsqc
  exact b2_constants hG hmax hP hv ha hc hac h1 h2 hna hnc hROa hROc hsqa hsqc

end Langlands.GroupScheme
