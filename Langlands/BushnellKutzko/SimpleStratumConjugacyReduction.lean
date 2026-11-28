import Langlands.BushnellKutzko.SimpleStratumConjugacyStep
import Langlands.BushnellKutzko.SimpleStratumConjugacyStatement
import Langlands.BushnellKutzko.SimpleCharacterCore

/-! # Formal intertwining and conjugacy of simple strata, from simple approximation

The induction of the proof of BK93 (2.6.1), printed pp. 83–86, runs from `t = n − 1` down
to `t = r`. This file assembles it and proves `SimpleStratumConjugacyStatement` from
`PureStratumSimpleApproximationStatement` (BK93 (2.4.1)(i)). The second clause of the
statement, the case of equal orders and levels of BK93 (2.6.2), uses no approximation.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SimpleConjugacy

open CriticalDerived

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {𝓛 : LatticeChain 𝒪[F] F V}

local notation "P" => 𝓛.endFiltration
local notation "A" => Module.End F V

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Conjugation by a unit of `𝔄` preserves pure elements. -/
theorem IsPureElement.conj {n : ℤ} {β : A} (h : IsPureElement 𝓛 n β) {u : Aˣ}
    (hu : Shifts 𝓛 0 u) : IsPureElement 𝓛 n ((u : A) * β * ((u⁻¹ : Aˣ) : A)) := by
  obtain ⟨S, rfl, rfl, rfl, hS⟩ := h
  have hg : ((u⁻¹ : Aˣ) : A) ∈ S.chain.endFiltration 0 := by simpa using hu.2
  have hg' : (((u⁻¹)⁻¹ : Aˣ) : A) ∈ S.chain.endFiltration 0 := by simpa using hu.1
  obtain ⟨⟨hf, hn⟩, hv⟩ := hS
  have hN := normalizingUnits_of_isField S.chain hf hn
  have hN' := normalizingUnits_conj S.chain hN
    (PureApproximation.mem_stabilizer_of_mem_order S.chain hg hg')
  have hval := PureApproximation.valuation_conj S.chain hg hg' S.b
  rw [PureApproximation.conjAlgHom_apply, inv_inv] at hval
  rw [inv_inv] at hN'
  refine ⟨⟨S.chain, S.n, S.r, (u : A) * S.b * ((u⁻¹ : Aˣ) : A), S.r_lt_n, ?_⟩,
    rfl, rfl, rfl, isField_of_normalizingUnits S.chain hN', ?_⟩
  · rw [hval]
    exact S.valuation_ge
  · exact hval.trans hv

/-- **BK93 (2.6.1), for pure strata on one chain.** Let `β₁, β₂` be the elements of pure
strata `[𝓛,n,r,β_i]` whose cosets `β_i + 𝔓^{−r}` are intertwined. Assuming BK93 (2.4.1)(i),
a unit `u` of `𝔄` satisfies `u β₂ u⁻¹ ∈ β₁ + 𝔓^{−r}`. -/
theorem exists_conj_of_isPureElement (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    [FiniteDimensional F V] {n r : ℤ} (hr : r < n) {β₁ β₂ : A}
    (h₁ : IsPureElement 𝓛 n β₁) (h₂ : IsPureElement 𝓛 n β₂) {g : Aˣ} {y : A}
    (hy : y - β₂ ∈ P (-r)) (hgy : ((g⁻¹ : Aˣ) : A) * y * g - β₁ ∈ P (-r)) :
    ∃ u : Aˣ, Shifts 𝓛 0 u ∧ (u : A) * β₂ * ((u⁻¹ : Aˣ) : A) - β₁ ∈ P (-r) := by
  -- conjugacy modulo `𝔓^{−(n−1−k)}`, by induction on `k`
  have key : ∀ k : ℕ, (k : ℤ) ≤ n - 1 - r →
      ∃ u : Aˣ, Shifts 𝓛 0 u ∧
        (u : A) * β₂ * ((u⁻¹ : Aˣ) : A) - β₁ ∈ P (-(n - 1 - k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hpn (β : A) (hβ : IsPureElement 𝓛 n β) : PureOrNull 𝓛 n β := by
        obtain ⟨S, hSc, hSn, hSb, hS⟩ := hβ
        have h := pureOrNull_of_isPure 𝓛 S hSc hS (c := β) (by rw [hSb, sub_self]; exact zero_mem _)
        rwa [hSn] at h
      have hle : P (-r) ≤ P (1 - n) := 𝓛.endFiltration_antitone (by omega)
      obtain ⟨u, hu, hmem⟩ := exists_conj_of_pureOrNull 𝓛 (hpn β₁ h₁) (hpn β₂ h₂)
        (hle hy) (hle hgy)
      refine ⟨u, hu, ?_⟩
      rwa [show -(n - 1 - ((0 : ℕ) : ℤ)) = 1 - n by push_cast; ring]
    | succ k ih =>
      intro hk
      obtain ⟨u, hu, hmem⟩ := ih (by push_cast at hk; omega)
      set t : ℤ := n - 1 - k with ht
      have htn : t < n := by omega
      have hle : P (-r) ≤ P (1 - t) := 𝓛.endFiltration_antitone (by push_cast at hk; omega)
      have h₂' := h₂.conj hu
      have hy' : (u : A) * y * ((u⁻¹ : Aˣ) : A) - (u : A) * β₂ * ((u⁻¹ : Aˣ) : A) ∈ P (1 - t) := by
        rw [show (u : A) * y * ((u⁻¹ : Aˣ) : A) - (u : A) * β₂ * ((u⁻¹ : Aˣ) : A) =
          (u : A) * (y - β₂) * ((u⁻¹ : Aˣ) : A) by noncomm_ring]
        exact conj_mem_of_shifts_zero 𝓛 hu (hle hy)
      have hgy' : (((u * g)⁻¹ : Aˣ) : A) * ((u : A) * y * ((u⁻¹ : Aˣ) : A)) * ↑(u * g) - β₁ ∈
          P (1 - t) := by
        have he : (((u * g)⁻¹ : Aˣ) : A) * ((u : A) * y * ((u⁻¹ : Aˣ) : A)) * ↑(u * g) =
            ((g⁻¹ : Aˣ) : A) * y * g := by
          simp only [mul_inv_rev, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
        rw [he]
        exact hle hgy
      obtain ⟨u', hu', hmem'⟩ := exists_conj_step hApprox htn h₁ h₂' hmem hy' hgy'
      refine ⟨u' * u, by simpa only [add_zero] using hu'.mul hu, ?_⟩
      have he : (↑(u' * u) : A) * β₂ * ↑(u' * u)⁻¹ =
          (u' : A) * ((u : A) * β₂ * ((u⁻¹ : Aˣ) : A)) * ↑u'⁻¹ := by
        simp only [mul_inv_rev, Units.val_mul, mul_assoc]
      rw [he, show -(n - 1 - ((k + 1 : ℕ) : ℤ)) = 1 - t by push_cast; ring]
      exact hmem'
  obtain ⟨u, hu, hmem⟩ := key (n - 1 - r).toNat (by omega)
  refine ⟨u, hu, ?_⟩
  rwa [show -(n - 1 - ((n - 1 - r).toNat : ℤ)) = -r by omega] at hmem

end Langlands.BushnellKutzko.SimpleConjugacy

namespace Langlands.BushnellKutzko

open SimpleConjugacy

universe uF uV

/-- **BK93 (2.6.1) and the case of equal orders and levels of BK93 (2.6.2)**, printed
pp. 83–86, assuming the simple approximation theorem BK93 (2.4.1)(i). -/
theorem simpleStratumConjugacy_of_approximation
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV}) :
    SimpleStratumConjugacyStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _
  refine ⟨fun S T hord hn hr hS hT hI => ?_, fun S T Z _ hr hT hST hZo _ hZr hZb => ?_⟩
  · obtain ⟨g, y, hy, hgy⟩ := hI
    have hP : T.chain.endFiltration = S.chain.endFiltration :=
      LatticeChain.endFiltration_eq_of_order_eq hord.symm
    have hTp : IsPureElement S.chain S.n T.b :=
      ⟨T.withChainAndLevel S.chain S.n hord hn, rfl, rfl, rfl,
        (Stratum.isSimple_withChainAndLevel T S.chain S.n hord hn hT).1⟩
    have hy' : y - T.b ∈ S.chain.endFiltration (-S.r) := by
      have h : y - T.b ∈ T.chain.endFiltration (-T.r) := hy
      rwa [hP, ← hr] at h
    obtain ⟨u, hu, hmem⟩ := exists_conj_of_isPureElement hApprox S.r_lt_n
      (isPureElement_of_isPure hS.1) hTp hy' hgy
    refine ⟨u, (S.chain.mem_unitFiltration_zero).mpr
      ⟨S.chain.mem_order_iff_mem_endFiltration.mpr hu.1,
        S.chain.mem_order_iff_mem_endFiltration.mpr (by simpa using hu.2)⟩, hmem⟩
  · rintro ⟨g, y, hy, hgy⟩
    have hP := StratumEquivalence.endFiltration_eq_of_equivalent hST
    have hrT := StratumEquivalence.r_eq_of_equivalent hST
    have hZP : Z.chain.endFiltration = S.chain.endFiltration :=
      LatticeChain.endFiltration_eq_of_order_eq hZo
    have hTn := T.r_lt_n
    have hyT : y - T.b ∈ T.chain.endFiltration (1 - T.n) := by
      have h : y ∈ T.coset := by
        rw [← show S.coset = T.coset from hST]
        exact hy
      exact T.chain.endFiltration_antitone (by omega) h
    apply conj_not_mem_of_isPure T hT.1 hyT g
    have h : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * y * g - Z.b ∈
        Z.chain.endFiltration (-Z.r) := hgy
    rw [hZb, sub_zero, hZP, hZr, hr, hP] at h
    exact T.chain.endFiltration_antitone (by omega) h

end Langlands.BushnellKutzko
