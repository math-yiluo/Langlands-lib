import Langlands.BushnellKutzko.NonsplitRefinementProof
import Langlands.BushnellKutzko.LatticeChainShifts
import Langlands.BushnellKutzko.RefinementProof

/-! # Units of a hereditary order under conjugation, and pure cosets

No unit of `𝔄` is conjugate into `𝔓`. Consequently the coset `β + 𝔓^{1−n}` of a pure
stratum `[𝔄,n,r,β]` has no element conjugate into `𝔓^{1−n}`. This is the case of equal
orders and levels of BK93 (2.6.2), printed p. 86.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SimpleConjugacy

open CriticalDerived

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration
local notation "A" => Module.End F V

/-- A unit `W` of `𝔄` (that is, `W, W⁻¹ ∈ 𝔄`) is never conjugate into `𝔓 = 𝔓^1`. -/
theorem conj_not_mem_one {W : Aˣ} (hW : Shifts 𝓛 0 W) (g : Aˣ) :
    ((g⁻¹ : Aˣ) : A) * W * g ∉ P 1 := by
  intro hX
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨t, ht⟩ := 𝓛.exists_uniformizer_pow_mem_endFiltration hϖ (g : A) 0
  obtain ⟨t', ht'⟩ := 𝓛.exists_uniformizer_pow_mem_endFiltration hϖ ((g⁻¹ : Aˣ) : A) 0
  set k : ℕ := (t + t') * 𝓛.period + 1 with hk
  let X : Aˣ := g⁻¹ * W * g
  have hXk : ((X ^ k : Aˣ) : A) ∈ P ((k : ℕ) * (1 : ℤ)) := by
    rw [Units.val_pow_eq_pow_val]
    exact NonsplitRefinement.pow_mem_endFiltration 𝓛 hX k
  have hXk' : X ^ k = g⁻¹ * W ^ k * g := by
    have h := _root_.conj_pow (a := g⁻¹) (b := W) (i := k)
    simpa only [inv_inv] using h
  have hWinv : ((W⁻¹ ^ k : Aˣ) : A) ∈ P 0 := by
    have h := (hW.inv.pow k).1
    simpa only [neg_zero, mul_zero] using h
  have hkey : ((ϖ : F) ^ (t + t')) • (1 : A) =
      ((X ^ k : Aˣ) : A) * (((ϖ : F) ^ t' • ((g⁻¹ : Aˣ) : A)) * ((W⁻¹ ^ k : Aˣ) : A) *
        ((ϖ : F) ^ t • (g : A))) := by
    have hone : ((X ^ k : Aˣ) : A) * (((g⁻¹ : Aˣ) : A) * ((W⁻¹ ^ k : Aˣ) : A) * (g : A)) = 1 := by
      rw [hXk', ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← Units.val_one]
      congr 1
      group
    conv_lhs => rw [← hone]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add, mul_assoc]
  have hmem : ((ϖ : F) ^ (t + t')) • (1 : A) ∈ P (1 + (t + t' : ℕ) * 𝓛.period) := by
    rw [hkey]
    have h1 := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration ht' hWinv) ht
    have h2 := 𝓛.mul_mem_endFiltration hXk h1
    convert h2 using 2
    simp only [hk]
    push_cast
    ring
  have h1 : (1 : A) ∈ P 1 := (𝓛.uniformizer_pow_end_mem_iff hϖ (t + t') 1 1).mp hmem
  apply (𝓛.lattice_succ_lt 0).not_ge
  intro v hv
  simpa using h1 0 v hv

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Let every nonzero element of the subalgebra `R` be a unit normalizing the chain. A nonzero
element of `R` is a unit shifting the chain by its valuation. -/
theorem shifts_of_mem_normalizing {R : Subalgebra F A} (hN : NormalizingUnits 𝓛 R) {w : A}
    (hw : w ∈ R) (hw0 : w ≠ 0) :
    ∃ u : Aˣ, (u : A) = w ∧ ∃ s : ℤ, Shifts 𝓛 s u ∧ 𝓛.valuation w = (s : WithTop ℤ) := by
  obtain ⟨g, hg, hgs⟩ := hN w hw hw0
  refine ⟨g, hg, 𝓛.stabilizerValuation ⟨g, hgs⟩, Shifts.of_stabilizer ⟨g, hgs⟩, ?_⟩
  rw [← hg]
  exact 𝓛.valuation_eq_shift ⟨g, hgs⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Let every nonzero element of the subalgebra `R` be a unit normalizing the chain. An
element of `R` which lies in `𝔄` lies in `𝔓` or is a unit of `𝔄`. -/
theorem mem_one_or_shifts_zero {R : Subalgebra F A} (hN : NormalizingUnits 𝓛 R) {w : A}
    (hw : w ∈ R) (hw0 : w ∈ P 0) : w ∈ P 1 ∨ ∃ u : Aˣ, (u : A) = w ∧ Shifts 𝓛 0 u := by
  by_cases h0 : w = 0
  · exact Or.inl (h0 ▸ zero_mem _)
  obtain ⟨u, hu, s, hs, -⟩ := shifts_of_mem_normalizing 𝓛 hN hw h0
  have hs0 : 0 ≤ s := by
    have hle : 𝓛.lattice (0 + s) ≤ 𝓛.lattice 0 := by
      rw [← hs.map_lattice 0]
      rintro _ ⟨v, hv, rfl⟩
      have h := (hu ▸ hw0) 0 v hv
      simpa using h
    have := 𝓛.strictAnti.le_iff_ge.mp hle
    omega
  rcases eq_or_lt_of_le hs0 with h | h
  · exact Or.inr ⟨u, hu, h ▸ hs⟩
  · exact Or.inl (hu ▸ 𝓛.endFiltration_antitone (show (1 : ℤ) ≤ s by omega) hs.1)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The element of a pure stratum is a unit shifting the chain by `−n`, and every nonzero
element of its generated algebra is a unit normalizing the chain. -/
theorem exists_shifts_of_isPure (S : Stratum 𝒪[F] F V) (hS : S.IsPure) :
    ∃ B : Aˣ, (B : A) = S.b ∧ Shifts S.chain (-S.n) B ∧
      NormalizingUnits S.chain (elementAlgebra S.b) := by
  obtain ⟨⟨hf, hn⟩, hv⟩ := hS
  have hN := normalizingUnits_of_isField S.chain hf hn
  have hb0 : S.b ≠ 0 := by
    intro h
    rw [h, LatticeChain.valuation_zero] at hv
    exact WithTop.top_ne_coe hv
  obtain ⟨B, hB, s, hs, hval⟩ :=
    shifts_of_mem_normalizing S.chain hN (Algebra.self_mem_adjoin_singleton F S.b) hb0
  have hsn : s = -S.n := by
    rw [hv] at hval
    exact_mod_cast hval.symm
  exact ⟨B, hB, hsn ▸ hs, hN⟩

/-- No element of `B + 𝔓^{1−n}`, for a unit `B` shifting the chain by `−n`, is conjugate
into `𝔓^{1−n}`. -/
theorem conj_not_mem_of_shifts {n : ℤ} {B : Aˣ} (hBs : Shifts 𝓛 (-n) B) {y : A}
    (hy : y - B ∈ P (1 - n)) (g : Aˣ) : ((g⁻¹ : Aˣ) : A) * y * g ∉ P (1 - n) := by
  intro hX
  have hsym : SymbolEq 𝓛 (-n) y B := by
    refine ⟨?_, hBs.1, ?_⟩
    · rw [show y = (y - B) + (B : A) by abel]
      exact add_mem (𝓛.endFiltration_antitone (by omega) hy) hBs.1
    · rw [show -n + 1 = 1 - n by ring]
      exact hy
  obtain ⟨Y, hY, hYs⟩ := exists_unit_of_symbolEq_self 𝓛 hBs hsym
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let π : Aˣ := scalarEndUnit (LatticeChain.uniformizerAsUnit hϖ)
  have hπ : Shifts 𝓛 𝓛.period π := uniformizerUnit_shifts hϖ 𝓛
  set e : ℕ := 𝓛.period with he
  let W : Aˣ := Y ^ e * π ^ n
  have hW : Shifts 𝓛 0 W := by
    have h := (hYs.pow e).mul (hπ.zpow n)
    rwa [show (e : ℤ) * -n + n * (e : ℤ) = 0 by ring] at h
  have hconj : g⁻¹ * W * g = (g⁻¹ * Y * g) ^ e * π ^ n := by
    have hc : Commute (π ^ n) g := (scalarEndUnit_commutes _ g).zpow_left n
    have hp : (g⁻¹ * Y * g) ^ e = g⁻¹ * Y ^ e * g := by
      simpa only [inv_inv] using _root_.conj_pow (a := g⁻¹) (b := Y) (i := e)
    rw [hp]
    calc g⁻¹ * W * g = g⁻¹ * Y ^ e * (π ^ n * g) := by simp only [W, mul_assoc]
      _ = g⁻¹ * Y ^ e * (g * π ^ n) := by rw [hc.eq]
      _ = g⁻¹ * Y ^ e * g * π ^ n := by simp only [mul_assoc]
  apply conj_not_mem_one 𝓛 hW g
  have h1 : ((g⁻¹ * Y * g : Aˣ) : A) ∈ P (1 - n) := by
    simpa only [Units.val_mul, hY] using hX
  have h2 := 𝓛.mul_mem_endFiltration
    (NonsplitRefinement.pow_mem_endFiltration 𝓛 h1 e) (hπ.zpow n).1
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← hconj] at h2
  rw [Units.val_mul, Units.val_mul] at h2
  have hpos : (1 : ℤ) ≤ e := by exact_mod_cast 𝓛.period_pos
  exact 𝓛.endFiltration_antitone (by nlinarith) h2

/-- **The case of equal orders and levels of BK93 (2.6.2), printed p. 86.** For a pure
stratum `[𝔄,n,r,β]`, no element of `β + 𝔓^{1−n}` is conjugate into `𝔓^{1−n}`. -/
theorem conj_not_mem_of_isPure (S : Stratum 𝒪[F] F V) (hS : S.IsPure) {y : A}
    (hy : y - S.b ∈ S.chain.endFiltration (1 - S.n)) (g : Aˣ) :
    ((g⁻¹ : Aˣ) : A) * y * g ∉ S.chain.endFiltration (1 - S.n) := by
  obtain ⟨B, hB, hBs, -⟩ := exists_shifts_of_isPure S hS
  exact conj_not_mem_of_shifts S.chain hBs (hB ▸ hy) g

end Langlands.BushnellKutzko.SimpleConjugacy
