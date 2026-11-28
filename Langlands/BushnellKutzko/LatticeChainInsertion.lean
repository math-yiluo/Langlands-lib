import Langlands.BushnellKutzko.MoyReduction
import Langlands.BushnellKutzko.UnitFiltration

/-! # Inserting one lattice into a lattice chain

Let `𝓛 = (L_j)` be an `𝔬_F`-lattice chain in `F^ι` and let `M` be a lattice with
`L_{p+1} ⊊ M ⊊ L_p`. The lattices `L_j` together with the lattices `ϖ^k M`, `k ∈ ℤ`, form a
lattice chain `𝓜` (`LatticeChain.exists_insertLattice`). Its period is larger than that of `𝓛`,
and every `g ∈ U^1(𝓜)` lies in `U(𝓛)`, acts trivially on the layers `L_j / L_{j+1}` with
`j ≢ p` modulo the period, and satisfies `(g - 1) L_p ⊆ M` and `(g - 1) M ⊆ L_{p+1}`.

This is the refinement step of Bushnell–Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), proof of (8.1.5), printed p. 268 (PDF p. 280), and of Bushnell, *Hereditary
orders, Gauss sums and supercuspidal representations of GL_N* (1987), proof of Theorem 2′(i),
printed p. 197 (PDF p. 14): a proper parabolic subgroup of `U(𝔄) / U^1(𝔄)` is the image of
`U(𝔄')` for a strictly finer lattice chain.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ι : Type v}

namespace LatticeChain

/-- **Inserting one lattice into a chain.** Let `M` be a lattice with `L_{p+1} ⊊ M ⊊ L_p`.
There is a lattice chain `𝓜` of larger period such that every `g ∈ U^1(𝓜)` lies in `U(𝓛)`,
satisfies `(g - 1) L_j ⊆ L_{j+1}` for every `j ≠ p` with `|j - p| < e(𝓛)`, and satisfies
`(g - 1) L_p ⊆ M` and `(g - 1) M ⊆ L_{p+1}`. The lattices of `𝓜` are the `L_j` and the
`ϖ^k M`. -/
theorem exists_insertLattice (𝓛 : LatticeChain 𝒪[F] F (ι → F)) {p : ℤ}
    {M : Submodule 𝒪[F] (ι → F)} (h₁ : 𝓛.lattice (p + 1) < M) (h₂ : M < 𝓛.lattice p) :
    ∃ 𝓜 : LatticeChain 𝒪[F] F (ι → F), 𝓛.period < 𝓜.period ∧
      ∀ g ∈ 𝓜.unitFiltration 1, g ∈ 𝓛.unitFiltration 0 ∧
        (∀ j : ℤ, j ≠ p → p < j + 𝓛.period → j < p + 𝓛.period →
          ∀ v ∈ 𝓛.lattice j, (g : Module.End F (ι → F)) v - v ∈ 𝓛.lattice (j + 1)) ∧
        (∀ v ∈ 𝓛.lattice p, (g : Module.End F (ι → F)) v - v ∈ M) ∧
        (∀ v ∈ M, (g : Module.End F (ι → F)) v - v ∈ 𝓛.lattice (p + 1)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  set u := uniformizerAsUnit hϖ with hu
  have he : (1 : ℤ) ≤ 𝓛.period := by exact_mod_cast 𝓛.period_pos
  have hMsw : 𝓛.IsSandwiched p M := ⟨h₁, h₂.le⟩
  have hsw : ∀ k : ℤ, 𝓛.IsSandwiched (p + 𝓛.period * k) (u ^ k • M) := fun k =>
    hMsw.zpow_smul hϖ k
  have hlt : ∀ k : ℤ, u ^ k • M < 𝓛.lattice (p + 𝓛.period * k) := fun k => by
    rw [lattice_add_period_mul hϖ]
    exact (units_smul_lt_units_smul_iff _).2 h₂
  have hanti_lt : ∀ {a b : ℤ}, 𝓛.lattice a < 𝓛.lattice b → b < a := fun h =>
    𝓛.strictAnti.lt_iff_gt.mp h
  let C : Set (Submodule 𝒪[F] (ι → F)) :=
    Set.range 𝓛.lattice ∪ Set.range fun k : ℤ => u ^ k • M
  have hMC : M ∈ C := Or.inr ⟨0, by simp⟩
  have hCsw : ∀ N ∈ C, ∃ q, 𝓛.IsSandwiched q N := by
    rintro N (⟨j, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨j, isSandwiched_lattice j⟩
    · exact ⟨_, hsw k⟩
  have hMM : ∀ k l : ℤ, k < l → u ^ l • M < u ^ k • M := by
    intro k l hkl
    have h1 : (𝓛.period : ℤ) * k + 1 ≤ 𝓛.period * l := by nlinarith
    calc u ^ l • M < 𝓛.lattice (p + 𝓛.period * l) := hlt l
      _ ≤ 𝓛.lattice (p + 𝓛.period * k + 1) := 𝓛.antitone (by omega)
      _ < u ^ k • M := (hsw k).1
  have hchain : IsChain (· ≤ ·) C := by
    rintro N₁ (⟨j, rfl⟩ | ⟨k, rfl⟩) N₂ hN₂ -
    · obtain ⟨q, hq⟩ := hCsw N₂ hN₂
      exact (hq.le_or_le j).symm
    · rcases hN₂ with ⟨j, rfl⟩ | ⟨l, rfl⟩
      · exact (hsw k).le_or_le j
      · rcases lt_trichotomy k l with hkl | rfl | hkl
        · exact Or.inr (hMM k l hkl).le
        · exact Or.inl le_rfl
        · exact Or.inl (hMM l k hkl).le
  have hsmul : ∀ N ∈ C, ∀ k : ℤ, u ^ k • N ∈ C := by
    rintro N (⟨j, rfl⟩ | ⟨l, rfl⟩) k
    · exact Or.inl ⟨j + 𝓛.period * k, lattice_add_period_mul hϖ 𝓛 j k⟩
    · refine Or.inr ⟨k + l, ?_⟩
      show u ^ (k + l) • M = u ^ k • u ^ l • M
      rw [smul_smul, ← zpow_add]
  have hClt : ∀ N ∈ C, u • N < N := fun N hN => by
    obtain ⟨q, hq⟩ := hCsw N hN
    exact hq.uniformizer_smul_lt hϖ
  have hfin : ∀ L ∈ C, ∀ L' ∈ C, {N | N ∈ C ∧ L' ≤ N ∧ N ≤ L}.Finite := by
    intro L hL L' hL'
    obtain ⟨P, hP⟩ := hCsw L hL
    obtain ⟨P', hP'⟩ := hCsw L' hL'
    refine (((Set.finite_Icc P P').image 𝓛.lattice).union
      ((Set.finite_Icc (-|P - p|) (|P' - p|)).image fun k : ℤ => u ^ k • M)).subset ?_
    rintro N ⟨hN, hN₁, hN₂⟩
    rcases hN with ⟨j, rfl⟩ | ⟨k, rfl⟩
    · have h1 := hP'.le_of_le (isSandwiched_lattice j) hN₁
      have h2 := (isSandwiched_lattice j).le_of_le hP hN₂
      exact Or.inl ⟨j, ⟨h2, h1⟩, rfl⟩
    · have h1 := hP'.le_of_le (hsw k) hN₁
      have h2 := (hsw k).le_of_le hP hN₂
      refine Or.inr ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rcases le_or_gt 0 k with hk | hk
        · linarith [abs_nonneg (P - p)]
        · nlinarith [neg_abs_le (P - p)]
      · rcases le_or_gt k 0 with hk | hk
        · linarith [abs_nonneg (P' - p)]
        · nlinarith [le_abs_self (P' - p)]
  obtain ⟨𝓜, h𝓜⟩ := exists_latticeChain_range_eq hϖ C
    (fun N hN => (hCsw N hN).choose_spec.isLattice) hchain ⟨M, hMC⟩ hsmul hClt hfin
  have hmemM : ∀ t, 𝓜.lattice t ∈ C := fun t => h𝓜 ▸ Set.mem_range_self t
  have hrangeM : ∀ N ∈ C, ∃ t, 𝓜.lattice t = N := fun N hN => by
    rw [← h𝓜] at hN
    exact hN
  -- A member of `C` with no member of `C` strictly between it and `𝓜_t` is `𝓜_{t+1}`.
  have hnext : ∀ (t : ℤ) (B : Submodule 𝒪[F] (ι → F)), B ∈ C → B < 𝓜.lattice t →
      (∀ N ∈ C, B < N → N < 𝓜.lattice t → False) → 𝓜.lattice (t + 1) = B := by
    intro t B hB hBt hgap
    obtain ⟨s, rfl⟩ := hrangeM B hB
    have hts : t < s := 𝓜.strictAnti.lt_iff_gt.mp hBt
    rcases (show s = t + 1 ∨ t + 1 < s by omega) with rfl | hs
    · rfl
    · exact (hgap _ (hmemM (t + 1)) (𝓜.strictAnti hs) (𝓜.strictAnti (lt_add_one t))).elim
  have hsplit : ∀ N ∈ C, (∃ j, N = 𝓛.lattice j) ∨ ∃ k : ℤ, N = u ^ k • M ∧
      𝓛.lattice (p + 𝓛.period * k + 1) < N ∧ N < 𝓛.lattice (p + 𝓛.period * k) := by
    rintro N (⟨j, rfl⟩ | ⟨k, rfl⟩)
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨k, rfl, (hsw k).1, hlt k⟩
  have hk0 : ∀ k : ℤ, (𝓛.period : ℤ) * k = 0 → k = 0 := fun k hk => by
    rcases mul_eq_zero.mp hk with h | h
    · omega
    · exact h
  -- No member of `C` lies strictly between `M` and `L_p`.
  have gap₁ : ∀ N ∈ C, M < N → N < 𝓛.lattice p → False := by
    intro N hN hMN hNp
    rcases hsplit N hN with ⟨j, rfl⟩ | ⟨k, rfl, hk₁, hk₂⟩
    · have hpj := hanti_lt hNp
      exact lt_asymm hMN ((𝓛.antitone (show p + 1 ≤ j by omega)).trans_lt h₁)
    · have ha := hanti_lt (hk₁.trans hNp)
      have hb := hanti_lt (h₁.trans (hMN.trans hk₂))
      have hk : k = 0 := hk0 k (by omega)
      subst hk
      simp at hMN
  -- No member of `C` lies strictly between `L_{p+1}` and `M`.
  have gap₂ : ∀ N ∈ C, 𝓛.lattice (p + 1) < N → N < M → False := by
    intro N hN hpN hNM
    rcases hsplit N hN with ⟨j, rfl⟩ | ⟨k, rfl, hk₁, hk₂⟩
    · have hjp := hanti_lt hpN
      exact lt_asymm hNM (h₂.trans_le (𝓛.antitone (show j ≤ p by omega)))
    · have ha := hanti_lt (hpN.trans hk₂)
      have hb := hanti_lt (hk₁.trans (hNM.trans h₂))
      have hk : k = 0 := hk0 k (by omega)
      subst hk
      simp at hNM
  -- No member of `C` lies strictly between `L_{j+1}` and `L_j` for `j ≢ p`.
  have gap₃ : ∀ j : ℤ, j ≠ p → p < j + 𝓛.period → j < p + 𝓛.period →
      ∀ N ∈ C, 𝓛.lattice (j + 1) < N → N < 𝓛.lattice j → False := by
    intro j hjp hj₁ hj₂ N hN hjN hNj
    rcases hsplit N hN with ⟨i, rfl⟩ | ⟨k, rfl, hk₁, hk₂⟩
    · have := hanti_lt hjN
      have := hanti_lt hNj
      omega
    · have ha := hanti_lt (hjN.trans hk₂)
      have hb := hanti_lt (hk₁.trans hNj)
      rcases lt_trichotomy k 0 with hk | rfl | hk
      · nlinarith
      · simp only [mul_zero, add_zero] at ha hb
        omega
      · nlinarith
  choose σ hσ using fun j : ℤ => hrangeM (𝓛.lattice j) (Or.inl ⟨j, rfl⟩)
  have hA : ∀ j : ℤ, j ≠ p → p < j + 𝓛.period → j < p + 𝓛.period →
      𝓜.lattice (σ j + 1) = 𝓛.lattice (j + 1) := by
    intro j hjp hj₁ hj₂
    refine hnext (σ j) _ (Or.inl ⟨_, rfl⟩) (by rw [hσ]; exact 𝓛.lattice_succ_lt j) ?_
    intro N hN hN₁ hN₂
    rw [hσ] at hN₂
    exact gap₃ j hjp hj₁ hj₂ N hN hN₁ hN₂
  have hB : 𝓜.lattice (σ p + 1) = M := by
    refine hnext (σ p) M hMC (by rw [hσ]; exact h₂) ?_
    intro N hN hN₁ hN₂
    rw [hσ] at hN₂
    exact gap₁ N hN hN₁ hN₂
  have hC : 𝓜.lattice (σ p + 1 + 1) = 𝓛.lattice (p + 1) := by
    refine hnext (σ p + 1) _ (Or.inl ⟨_, rfl⟩) (by rw [hB]; exact h₁) ?_
    intro N hN hN₁ hN₂
    rw [hB] at hN₂
    exact gap₂ N hN hN₁ hN₂
  -- The period of `𝓜` is larger.
  have hσmono : StrictMono σ := by
    intro a b hab
    have h : 𝓜.lattice (σ b) < 𝓜.lattice (σ a) := by
      rw [hσ, hσ]
      exact 𝓛.strictAnti hab
    exact 𝓜.strictAnti.lt_iff_gt.mp h
  have hσp1 : σ (p + 1) = σ p + 1 + 1 := by
    apply 𝓜.injective
    rw [hσ, hC]
  have hσper : σ (p + 𝓛.period) = σ p + 𝓜.period := by
    apply 𝓜.injective
    rw [hσ, 𝓜.lattice_add_period, hσ, 𝓛.lattice_add_period]
  have hσgap : ∀ (a : ℤ) (n : ℕ), (n : ℤ) ≤ σ (a + n) - σ a := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hσmono (lt_add_one (a + n))
      have h2 : a + ((n + 1 : ℕ) : ℤ) = a + n + 1 := by push_cast; ring
      rw [h2]
      omega
  have hper : 𝓛.period < 𝓜.period := by
    have h := hσgap (p + 1) (𝓛.period - 1)
    have h3 : p + 1 + ((𝓛.period - 1 : ℕ) : ℤ) = p + 𝓛.period := by
      have := 𝓛.period_pos
      omega
    rw [h3, hσper, hσp1] at h
    omega
  refine ⟨𝓜, hper, fun g hg => ⟨?_, ?_, ?_, ?_⟩⟩
  · have hpres : ∀ x ∈ 𝓜.order, x ∈ 𝓛.order := by
      intro x hx
      rw [mem_order]
      intro j v hv
      rw [← hσ] at hv ⊢
      exact (𝓜.mem_order.mp hx) _ v hv
    exact 𝓛.mem_unitFiltration_zero.mpr ⟨hpres _ hg.1, hpres _ hg.2.1⟩
  · intro j hjp hj₁ hj₂ v hv
    rw [← hσ] at hv
    rw [← hA j hjp hj₁ hj₂]
    simpa using hg.2.2 (σ j) v hv
  · intro v hv
    rw [← hσ] at hv
    rw [← hB]
    simpa using hg.2.2 (σ p) v hv
  · intro v hv
    rw [← hB] at hv
    rw [← hC]
    simpa using hg.2.2 (σ p + 1) v hv

end LatticeChain

end Langlands.BushnellKutzko
