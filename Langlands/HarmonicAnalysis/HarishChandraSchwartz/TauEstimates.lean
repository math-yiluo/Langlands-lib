import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalBounds
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalLevi

/-! # Lemmas II.3.2, II.3.3 and II.3.4 from properties of the representations `τ_P`

Waldspurger 2003, II.2: for a standard parabolic subgroup `P = M U` there is an algebraic
representation `τ_P` of `G` on a space `E_P` with a basis `(e_i)` and a height
`‖·‖ = sup |x_i|`, such that `τ_P(m u) e_1 = δ_P^{alg}(m) e_1`, `A_0` acts diagonally by
characters, `K` acts by operators of bounded norm, and `1 + σ(ū) ≍ 1 + log ‖τ_P(ū) e_1‖`
on `Ū` (II.2 (1)–(6)). Lemmas II.3.2, II.3.3 and II.3.4 are deduced from these
properties. This module states the properties of `τ_P` actually used, through the
functions `N(g) = ‖τ(g) e_1‖` and `ψ(g) = log ‖τ(g) e_1‖`, as explicit hypotheses, and
proves the three lemmas from them. The conclusions are the hypotheses
`CartanWeightComparison` (Lemma II.3.2, used for Lemma II.4.4) and
`LevelHeightComparison` (Lemma II.3.4, used for Lemma II.4.2) of `SphericalBounds`.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Langlands.HarishChandraSchwartz

universe u

section CartanComparison

variable {G : Type u} [Group G] {P K : Subgroup G} {hPK : IsIwasawaPair P K}
  {δ : P →* ℝ≥0ˣ}

/-- Waldspurger, Lemma II.3.2, from properties of `N(g) = ‖τ_0(g) e_1‖`: if
`N(p⁻¹) = δ(p)⁻¹` for `p ∈ P` (II.2 (1), `‖e_1‖ = 1`), `N(k y) ≤ C N(y)` for `k ∈ K`
(II.2 (5)), `N(a⁻¹ y) ≤ δ(a)⁻¹ N(y)` for `a ∈ A` (the diagonal action of `Ā⁺_0` with
`|χ_i(a)|^{-1} ≤ 1`, II.2 (2), (3)), `N((k γ)⁻¹)` and `δ(γ)` are bounded for `k ∈ K`,
`γ ∈ Γ`, and every `s ∈ S` is `γ a` with `γ ∈ Γ`, `a ∈ A`, then
`δ(s) ≤ C δ(m_0(g))` for `g ∈ K s K`, in the form `CartanWeightComparison K S φ` for the
weight `φ(p k) = δ(p)^{1/2}`. For Waldspurger's data `S = M̄⁺_0`, `A = Ā⁺_0` and `Γ` is a
compact subset of `M_0` with `M̄⁺_0 ⊂ Γ Ā⁺_0`. -/
theorem cartanWeightComparison_of_norm (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1)
    {N : G → ℝ} {S : Set G} {Γ A : Set P}
    (hN : ∀ p : P, N ((p : G)⁻¹) = ((δ p : ℝ≥0) : ℝ)⁻¹)
    (hNK : ∃ C : ℝ, ∀ k ∈ K, ∀ y, N (k * y) ≤ C * N y)
    (hNA : ∀ a ∈ A, ∀ y, N ((a : G)⁻¹ * y) ≤ ((δ a : ℝ≥0) : ℝ)⁻¹ * N y)
    (hNΓ : ∃ C : ℝ, ∀ k ∈ K, ∀ γ ∈ Γ, N ((k * (γ : G))⁻¹) ≤ C)
    (hδΓ : ∃ C : ℝ, ∀ γ ∈ Γ, ((δ γ : ℝ≥0) : ℝ) ≤ C)
    (hcover : ∀ s ∈ S, ∃ γ ∈ Γ, ∃ a ∈ A, s = ((γ * a : P) : G)) :
    CartanWeightComparison K S (iwasawaWeight hPK δ) := by
  obtain ⟨CK, hNK⟩ := hNK
  obtain ⟨CΓ, hNΓ⟩ := hNΓ
  obtain ⟨Cδ, hδΓ⟩ := hδΓ
  have hd : ∀ p : P, 0 < ((δ p : ℝ≥0) : ℝ) := fun p => by
    have := (δ p).ne_zero
    positivity
  -- `C_K ≥ 1`, from `N(1) = 1`
  have hN1 : N 1 = 1 := by
    have h := hN 1
    simpa using h
  have hCK : 0 ≤ CK := by
    have h := hNK 1 K.one_mem 1
    rw [one_mul, hN1, mul_one] at h
    linarith
  refine ⟨Real.sqrt (CK * CΓ * Cδ), fun s hs k₁ hk₁ k₂ hk₂ => ?_⟩
  obtain ⟨γ, hγ, a, ha, rfl⟩ := hcover s hs
  set g := k₁ * ((γ * a : P) : G) * k₂
  obtain ⟨k, hk, hfac⟩ := exists_iwasawaFactor hPK g
  set p := iwasawaFactor hPK g
  -- `p⁻¹ = (k k₂⁻¹) a⁻¹ (k₁ γ)⁻¹`
  have hpinv : ((p : G))⁻¹ = (k * k₂⁻¹) * ((a : G)⁻¹ * (k₁ * (γ : G))⁻¹) := by
    have : (p : G) = g * k⁻¹ := by rw [hfac]; group
    rw [this]
    simp only [g, Subgroup.coe_mul]
    group
  have hkey : ((δ p : ℝ≥0) : ℝ)⁻¹ ≤ CK * (((δ a : ℝ≥0) : ℝ)⁻¹ * CΓ) := by
    rw [← hN p, hpinv]
    calc N ((k * k₂⁻¹) * ((a : G)⁻¹ * (k₁ * (γ : G))⁻¹))
        ≤ CK * N ((a : G)⁻¹ * (k₁ * (γ : G))⁻¹) :=
          hNK _ (K.mul_mem hk (K.inv_mem hk₂)) _
      _ ≤ CK * (((δ a : ℝ≥0) : ℝ)⁻¹ * N ((k₁ * (γ : G))⁻¹)) :=
          mul_le_mul_of_nonneg_left (hNA a ha _) hCK
      _ ≤ CK * (((δ a : ℝ≥0) : ℝ)⁻¹ * CΓ) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hNΓ k₁ hk₁ γ hγ) (inv_nonneg.mpr (hd a).le)) hCK
  have hsa : ((δ (γ * a) : ℝ≥0) : ℝ) = ((δ γ : ℝ≥0) : ℝ) * ((δ a : ℝ≥0) : ℝ) := by
    rw [map_mul, Units.val_mul, NNReal.coe_mul]
  -- `δ(γ a) ≤ C δ(p)`
  have hmain : ((δ (γ * a) : ℝ≥0) : ℝ) ≤ CK * CΓ * Cδ * ((δ p : ℝ≥0) : ℝ) := by
    have h1 : ((δ p : ℝ≥0) : ℝ)⁻¹ * ((δ a : ℝ≥0) : ℝ) ≤ CK * CΓ := by
      calc ((δ p : ℝ≥0) : ℝ)⁻¹ * ((δ a : ℝ≥0) : ℝ)
          ≤ CK * (((δ a : ℝ≥0) : ℝ)⁻¹ * CΓ) * ((δ a : ℝ≥0) : ℝ) :=
            mul_le_mul_of_nonneg_right hkey (hd a).le
        _ = CK * CΓ := by field_simp [(hd a).ne']
    have h2 : ((δ a : ℝ≥0) : ℝ) ≤ CK * CΓ * ((δ p : ℝ≥0) : ℝ) := by
      have := mul_le_mul_of_nonneg_right h1 (hd p).le
      rwa [mul_comm (((δ p : ℝ≥0) : ℝ)⁻¹), mul_assoc, inv_mul_cancel₀ (hd p).ne', mul_one]
        at this
    rw [hsa]
    have hγC := hδΓ γ hγ
    have hCKΓ : 0 ≤ CK * CΓ * ((δ p : ℝ≥0) : ℝ) := le_trans (hd a).le h2
    calc ((δ γ : ℝ≥0) : ℝ) * ((δ a : ℝ≥0) : ℝ)
        ≤ Cδ * (CK * CΓ * ((δ p : ℝ≥0) : ℝ)) :=
          mul_le_mul hγC h2 (hd a).le (le_trans (hd γ).le hγC)
      _ = CK * CΓ * Cδ * ((δ p : ℝ≥0) : ℝ) := by ring
  -- the weights
  have hφs : iwasawaWeight hPK δ ((γ * a : P) : G) =
      NNReal.sqrt (δ (γ * a) : ℝ≥0) := by
    have h := iwasawaWeight_mul (hPK := hPK) hδ (γ * a).2 K.one_mem
    rw [mul_one] at h
    exact h
  have hφg : iwasawaWeight hPK δ g = NNReal.sqrt (δ p : ℝ≥0) := by
    rw [hfac, iwasawaWeight_mul (hPK := hPK) hδ p.2 hk]
  rw [hφs, hφg, Real.coe_sqrt, Real.coe_sqrt]
  have hC0 : 0 ≤ CK * CΓ * Cδ := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg (hd p)
    linarith [hd (γ * a)]
  rw [← Real.sqrt_mul hC0]
  exact Real.sqrt_le_sqrt hmain

end CartanComparison

section ConjugationHeight

variable {G : Type u} [Group G] {M U : Subgroup G}

/-- Waldspurger, Lemma II.3.3, from properties of `ψ(g) = log ‖τ_0(g) e_1‖`: if
`1 + σ ≍ 1 + ψ` on `U` (II.2 (6)), conjugation `u ↦ a⁻¹ u a` by `a ∈ T` maps `U` to itself
and does not increase `ψ` (the diagonal action of `Ā⁺_0`, II.2 (2), (3)), the elements of
`T` commute with `M`, `σ` is subadditive, and the second inequality of Lemma II.3.1 holds
for `(M, U)`, then `1 + σ(a⁻¹ m u a) ≤ C (1 + σ(m u))`. For Waldspurger's data
`M U = M_0 Ū_0 = P̄_0` and `T = Ā⁺_0`; the statement for `P_0` follows by exchanging
`P_0` and `P̄_0`. -/
theorem conj_height_le_of_tau {T : Set G} {ψ σ : G → ℝ}
    (h6 : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ u : U,
      C₁ * (1 + ψ u) ≤ 1 + σ u ∧ 1 + σ u ≤ C₂ * (1 + ψ u))
    (hTU : ∀ a ∈ T, ∀ u : U, a⁻¹ * u * a ∈ U)
    (hcontr : ∀ a ∈ T, ∀ u : U, ψ (a⁻¹ * u * a) ≤ ψ u)
    (hcomm : ∀ a ∈ T, ∀ m : M, a * m = m * a)
    (h31 : SigmaProductBound M U σ) (hσ : ∀ g, 0 ≤ σ g)
    (hsub : ∀ x y, σ (x * y) ≤ σ x + σ y) :
    ∃ C : ℝ, ∀ a ∈ T, ∀ m : M, ∀ u : U,
      1 + σ (a⁻¹ * ((m : G) * u) * a) ≤ C * (1 + σ ((m : G) * u)) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h6⟩ := h6
  obtain ⟨C, hC, h31⟩ := h31
  refine ⟨2 * (1 + C₂ / C₁) / C, fun a ha m u => ?_⟩
  set u' : U := ⟨a⁻¹ * u * a, hTU a ha u⟩
  have hconj : a⁻¹ * ((m : G) * u) * a = (m : G) * u' := by
    have h := hcomm a ha m
    have h' : a⁻¹ * (m : G) = (m : G) * a⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_assoc, mul_inv_cancel, mul_one]
    calc a⁻¹ * ((m : G) * u) * a = (a⁻¹ * (m : G)) * u * a := by group
      _ = ((m : G) * a⁻¹) * u * a := by rw [h']
      _ = (m : G) * u' := by simp only [u']; group
  have h1 : 1 + σ u' ≤ C₂ / C₁ * (1 + σ u) := by
    have hA := (h6 u').2
    have hB := (h6 u).1
    have hψ : ψ u' ≤ ψ u := hcontr a ha u
    rw [div_mul_eq_mul_div, le_div_iff₀ hC₁]
    calc (1 + σ u') * C₁ ≤ C₂ * (1 + ψ u') * C₁ := mul_le_mul_of_nonneg_right hA hC₁.le
      _ ≤ C₂ * (1 + ψ u) * C₁ := by gcongr
      _ = C₂ * (C₁ * (1 + ψ u)) := by ring
      _ ≤ C₂ * (1 + σ u) := mul_le_mul_of_nonneg_left hB hC₂.le
  have hmax := h31 m u
  have hmu : 1 + max (σ m) (σ u) ≥ 1 + σ m := by simp
  have hmu' : 1 + max (σ m) (σ u) ≥ 1 + σ u := by simp
  have hq : 0 ≤ C₂ / C₁ := div_nonneg hC₂.le hC₁.le
  rw [hconj]
  have hs := hsub (m : G) u'
  calc 1 + σ ((m : G) * u') ≤ (1 + σ m) + σ u' := by linarith
    _ ≤ (1 + σ m) + C₂ / C₁ * (1 + σ u) := by linarith
    _ ≤ (1 + C₂ / C₁) * (1 + max (σ m) (σ u)) +
          (1 + C₂ / C₁) * (1 + max (σ m) (σ u)) := by nlinarith [hσ m, hσ u]
    _ = 2 * (1 + C₂ / C₁) / C * (C * (1 + max (σ m) (σ u))) := by
        field_simp
        ring
    _ ≤ 2 * (1 + C₂ / C₁) / C * (1 + σ ((m : G) * u)) := by
        refine mul_le_mul_of_nonneg_left hmax ?_
        positivity

end ConjugationHeight

section ModulusHeight

variable {G : Type u} [Group G] {P K M U : Subgroup G} {hPK : IsIwasawaPair P K}

/-- The conclusion of Lemma II.3.4: there are `C₀`, `C₁ > 0`, `C₂ > 0`, `C₃ > 0` with
`C₁ (1 + σ(u)) ≤ C₀ - log δ(ℓ(u)) ≤ C₂ (1 + σ(ℓ(u))) ≤ C₃ (1 + σ(u))` for `u ∈ U`, where
`ℓ(u) = m_P(u)` is the Levi component and `δ = δ_P`. -/
def ModulusHeightBounds (U : Subgroup G) (σ : G → ℝ) (ℓ : G → M) (δ : M →* ℝ≥0ˣ) :
    Prop :=
  ∃ C₀ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ ∀ u : U,
    C₁ * (1 + σ u) ≤ C₀ - Real.log ((δ (ℓ u) : ℝ≥0) : ℝ) ∧
      C₀ - Real.log ((δ (ℓ u) : ℝ≥0) : ℝ) ≤ C₂ * (1 + σ (ℓ u)) ∧
      1 + σ (ℓ u) ≤ C₃ * (1 + σ u)

/-- Waldspurger, Lemma II.3.4, from properties of `ψ(g) = log ‖τ_P(g) e_1‖`: the upper
bound `1 + σ ≤ C (1 + ψ)` on `U` (II.2 (6)), `ψ((p k)⁻¹) ≤ C - log δ_P(m_P(p))` for
`p ∈ P`, `k ∈ K` (from II.2 (1), (5)), `-log δ_P(m) ≤ C (1 + σ(m))` on `M` (polynomiality
of `δ_P^{alg}`), `1 + σ(m_P(p)) ≤ C (1 + σ(p))` on `P` (from Lemma II.3.1), right
`K`-invariance and inversion invariance of `σ`, and `σ ≥ 0`. -/
theorem modulusHeightBounds_of_tau (mP : P →* M) (δ : M →* ℝ≥0ˣ) {ψ σ : G → ℝ}
    (h6 : ∃ C : ℝ, 0 < C ∧ ∀ u : U, 1 + σ u ≤ C * (1 + ψ u))
    (hψ : ∃ C : ℝ, ∀ p : P, ∀ k ∈ K,
      ψ (((p : G) * k)⁻¹) ≤ C - Real.log ((δ (mP p) : ℝ≥0) : ℝ))
    (hpoly : ∃ C : ℝ, ∀ m : M, -Real.log ((δ m : ℝ≥0) : ℝ) ≤ C * (1 + σ m))
    (hlevi : ∃ C : ℝ, ∀ p : P, 1 + σ (mP p) ≤ C * (1 + σ p))
    (hσK : ∀ g, ∀ k ∈ K, σ (g * k) = σ g) (hσinv : ∀ g, σ g⁻¹ = σ g)
    (hσ : ∀ g, 0 ≤ σ g) :
    ModulusHeightBounds U σ (leviComponent hPK mP) δ := by
  obtain ⟨C₆, hC₆, h6⟩ := h6
  obtain ⟨Cψ, hψ⟩ := hψ
  obtain ⟨C₄, hpoly⟩ := hpoly
  obtain ⟨C₅, hlevi⟩ := hlevi
  refine ⟨1 + Cψ, C₆⁻¹, |1 + Cψ| + |C₄| + 1, max C₅ 1, inv_pos.mpr hC₆, by positivity,
    lt_of_lt_of_le one_pos (le_max_right _ _), fun u => ⟨?_, ?_, ?_⟩⟩
  · -- `1 + σ(u) = 1 + σ(u⁻¹) ≤ C₆ (1 + ψ(u⁻¹)) ≤ C₆ (1 + Cψ - log δ_P(m_P(u)))`
    obtain ⟨k, hk, hfac⟩ := exists_iwasawaFactor hPK (u : G)
    have h1 := h6 u⁻¹
    have h2 := hψ (iwasawaFactor hPK u) k hk
    rw [← hfac] at h2
    simp only [Subgroup.coe_inv, hσinv] at h1
    rw [inv_mul_le_iff₀ hC₆]
    change 1 + σ (u : G) ≤ C₆ * (1 + Cψ - Real.log ((δ (mP (iwasawaFactor hPK u)) : ℝ≥0) : ℝ))
    nlinarith
  · -- `-log δ_P(m) ≤ C₄ (1 + σ(m))`
    have h1 := hpoly (leviComponent hPK mP u)
    have hσm := hσ (leviComponent hPK mP u)
    have ha : (1 + Cψ) ≤ |1 + Cψ| * (1 + σ (leviComponent hPK mP u)) := by
      have := le_abs_self (1 + Cψ)
      have := abs_nonneg (1 + Cψ)
      nlinarith
    have hb : C₄ * (1 + σ (leviComponent hPK mP u)) ≤
        |C₄| * (1 + σ (leviComponent hPK mP u)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    nlinarith
  · -- `1 + σ(m_P(u)) ≤ C₅ (1 + σ(p)) = C₅ (1 + σ(u))`
    obtain ⟨k, hk, hfac⟩ := exists_iwasawaFactor hPK (u : G)
    have h1 := hlevi (iwasawaFactor hPK u)
    have h2 : σ (iwasawaFactor hPK u : G) = σ (u : G) := by
      conv_rhs => rw [hfac]
      rw [hσK _ k hk]
    change 1 + σ (mP (iwasawaFactor hPK u)) ≤ max C₅ 1 * (1 + σ (u : G))
    rw [← h2]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [hσ (u : G)]))

/-- Lemma II.3.4 for `P_0` in the form used by Lemma II.4.2: if
`-log δ_0(m_0(u)) = N(u) log q` on `U`, the outer inequalities of `ModulusHeightBounds`
are `LevelHeightComparison U N q σ`. -/
theorem ModulusHeightBounds.levelHeightComparison {σ : G → ℝ} {ℓ : G → M}
    {δ : M →* ℝ≥0ˣ} (h : ModulusHeightBounds U σ ℓ δ) {N : U → ℤ} {q : ℝ}
    (hN : ∀ u : U, -Real.log ((δ (ℓ u) : ℝ≥0) : ℝ) = N u * Real.log q) :
    LevelHeightComparison U N q σ := by
  obtain ⟨C₀, C₁, C₂, C₃, hC₁, hC₂, hC₃, h⟩ := h
  refine ⟨C₀, C₁, C₂ * C₃, hC₁, mul_pos hC₂ hC₃, fun u => ⟨?_, ?_⟩⟩
  · have := (h u).1
    rw [sub_eq_add_neg, hN u] at this
    exact this
  · have h2 := (h u).2.1
    have h3 := (h u).2.2
    rw [sub_eq_add_neg, hN u] at h2
    calc C₀ + N u * Real.log q ≤ C₂ * (1 + σ (ℓ u)) := h2
      _ ≤ C₂ * (C₃ * (1 + σ u)) := mul_le_mul_of_nonneg_left h3 hC₂.le
      _ = C₂ * C₃ * (1 + σ u) := by ring

end ModulusHeight

end Langlands.HarishChandraSchwartz
