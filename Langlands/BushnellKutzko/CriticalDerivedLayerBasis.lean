import Langlands.BushnellKutzko.CriticalDerivedSymbols
import Langlands.BushnellKutzko.SplittingBasis

/-! # From bases of the layers to a splitting basis -/

noncomputable section

open ValuativeRel IsLocalRing
open scoped BigOperators

namespace Langlands.BushnellKutzko.CriticalDerived

open StratumEquivalence

universe uF uV uI

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)

include hϖ in
/-- A nonzero finite coefficient family has a common uniformizer factor with an integral
quotient family having at least one unit coefficient. -/
theorem exists_primitive_coeffs {I : Type uI} [Fintype I] (c : I → F) (hc : ∃ i, c i ≠ 0) :
    ∃ (t : ℤ) (r : I → 𝒪[F]), (∀ i, c i = (ϖ : F) ^ t * (r i : F)) ∧
      ∃ i, residue 𝒪[F] (r i) ≠ 0 := by
  classical
  let s := Finset.univ.filter (fun i => c i ≠ 0)
  have hs : s.Nonempty := by simpa [s, Finset.Nonempty] using hc
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image s (fun j => ordOf hϖ (c j)) hs
  let t := ordOf hϖ (c i)
  have hϖ0 := coe_uniformizer_ne_zero hϖ
  let r (j : I) : 𝒪[F] := ⟨(ϖ : F) ^ (-t) * c j, by
    by_cases hj : c j = 0
    · simp [hj]
    apply mem_integer_of_ordOf_nonneg hϖ (mul_ne_zero (zpow_ne_zero _ hϖ0) hj)
    rw [ordOf_mul hϖ (zpow_ne_zero _ hϖ0) hj, ordOf_zpow hϖ]
    simpa only [add_comm (-t), ← sub_eq_add_neg] using
      sub_nonneg.mpr (hmin j (by simpa [s] using hj))⟩
  refine ⟨t, r, fun j => ?_, i, ?_⟩
  · change c j = (ϖ : F) ^ t * ((ϖ : F) ^ (-t) * c j)
    rw [← mul_assoc, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, one_mul]
  · have hi0 : c i ≠ 0 := (Finset.mem_filter.mp hi).2
    obtain ⟨u, hu⟩ := exists_eq_zpow_ordOf_mul hϖ hi0
    have heq : r i = (u : 𝒪[F]) := by
      apply Subtype.ext
      change (ϖ : F) ^ (-t) * c i = ((u : 𝒪[F]) : F)
      rw [hu, ← mul_assoc, ← zpow_add₀ hϖ0]
      simp [t]
    rw [heq, residue_ne_zero_iff_isUnit]
    exact u.isUnit

variable {V : Type uV} [AddCommGroup V] [Module F V] (𝓒 : LatticeChain 𝒪[F] F V)

local notation "L" => 𝓒.lattice
local notation "e" => 𝓒.period
local notation "k" => ResidueField 𝒪[F]

/-- A sum of integral multiples can be reduced termwise on a layer. -/
theorem intervalMk_sum_smul {I : Type uI} [Fintype I] {j : ℤ} (r : I → 𝒪[F])
    (v : I → V) (hv : ∀ i, v i ∈ L j) :
    𝓒.intervalMk j (j + 1) (∑ i, (r i : F) • v i)
      (Submodule.sum_mem _ (fun i _ => (L j).smul_mem (r i) (hv i))) =
      ∑ i, residue 𝒪[F] (r i) • 𝓒.intervalMk j (j + 1) (v i) (hv i) := by
  let q := (𝓒.intervalSubmodule j (j + 1)).mkQ
  have h (i : I) (x : 𝓒.Layer j) : residue 𝒪[F] (r i) • x = r i • x :=
    algebraMap_smul (ResidueField 𝒪[F]) (r i) x
  simp only [h]
  change q ⟨_, _⟩ = ∑ i, r i • q ⟨v i, hv i⟩
  rw [show (⟨∑ i, (r i : F) • v i, _⟩ : L j) = ∑ i, r i • (⟨v i, hv i⟩ : L j) from ?_]
  · simp only [map_sum, map_smul]
  · apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    rfl

section LayerBases

variable {I : Fin 𝓒.period → Type uI} [∀ j, Fintype (I j)]
  (b : ∀ j : Fin 𝓒.period, Module.Basis (I j) (ResidueField 𝒪[F]) (𝓒.Layer (j : ℤ)))
  (v : (j : Fin 𝓒.period) → I j → V)
  (hv : ∀ (j : Fin 𝓒.period) (i : I j), v j i ∈ 𝓒.lattice (j : ℤ))
  (hb : ∀ (j : Fin 𝓒.period) (i : I j),
    𝓒.intervalMk (j : ℤ) ((j : ℤ) + 1) (v j i) (hv j i) = b j i)

include hv hb in
private theorem exists_layer_correction (j : Fin e) {w : V} (hw : w ∈ L (j : ℤ)) :
    ∃ r : I j → 𝒪[F], w - ∑ i, (r i : F) • v j i ∈ L ((j : ℤ) + 1) := by
  classical
  let w' := 𝓒.intervalMk (j : ℤ) ((j : ℤ) + 1) w hw
  choose r hr using fun i => residue_surjective ((b j).repr w' i)
  have hr' : ∑ i, (r i : F) • v j i ∈ L (j : ℤ) :=
    Submodule.sum_mem _ (fun i _ => (L (j : ℤ)).smul_mem (r i) (hv j i))
  refine ⟨r, (𝓒.intervalMk_eq_iff hw hr').mp ?_⟩
  rw [intervalMk_sum_smul 𝓒 r (v j) (hv j), show 𝓒.intervalMk (j : ℤ) ((j : ℤ) + 1) w hw = w' from rfl]
  simp only [hb, hr, Module.Basis.sum_repr]

include hv hb hϖ in
private theorem layerLifts_span : Submodule.span F (Set.range fun i : Sigma I => v i.1 i.2) = ⊤ := by
  classical
  let U := Submodule.span F (Set.range fun i : Sigma I => v i.1 i.2)
  apply eq_top_iff.mpr
  intro x _
  by_contra hx
  obtain ⟨w, hwx, hwmax⟩ := exists_lattice_maximal_coset_rep 𝓒 hϖ U hx
  have hwu : w ∉ U := fun h => hx (by simpa only [sub_sub_cancel] using sub_mem h hwx)
  have hw0 : w ≠ 0 := fun h => hwu (h.symm ▸ zero_mem U)
  let n := 𝓒.index hϖ w
  let t := n / (e : ℤ)
  have he : (0 : ℤ) < e := Int.natCast_pos.mpr 𝓒.period_pos
  have hm₀ := Int.emod_nonneg n he.ne'
  have hm₁ := Int.emod_lt_of_pos n he
  let j : Fin e := ⟨(n % (e : ℤ)).toNat, by omega⟩
  have hj : (j : ℤ) = n % (e : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ he.ne')
  have hn : (j : ℤ) + (e : ℤ) * t = n := by rw [hj]; exact Int.emod_add_mul_ediv n (e : ℤ)
  let w' := (ϖ : F) ^ (-t) • w
  have hw' : w' ∈ L (j : ℤ) := by
    rw [show w' = (ϖ : F) ^ (-t) • w from rfl, 𝓒.zpow_smul_mem_iff hϖ, mul_neg, sub_neg_eq_add, hn]
    exact 𝓒.mem_lattice_index hϖ hw0
  obtain ⟨r, hr⟩ := exists_layer_correction 𝓒 b v hv hb j hw'
  let y := ∑ i, (r i : F) • v j i
  have hy : y ∈ U := Submodule.sum_mem _ fun i _ =>
    U.smul_mem _ (Submodule.subset_span ⟨⟨j, i⟩, rfl⟩)
  have hd : w - (ϖ : F) ^ t • y ∈ L (n + 1) := by
    have h := (𝓒.zpow_smul_mem_iff hϖ t (j := n + 1) (x := w' - y)).mpr (by
      convert hr using 2
      omega)
    rw [smul_sub, show w' = _ from rfl, smul_smul, ← zpow_add₀ (coe_uniformizer_ne_zero hϖ),
      add_neg_cancel, zpow_zero, one_smul] at h
    exact h
  apply 𝓒.not_mem_lattice_index_add_one hϖ hw0
  apply hwmax (n + 1)
  refine ⟨_, hd, ?_⟩
  rw [show w - (ϖ : F) ^ t • y - x = (w - x) - (ϖ : F) ^ t • y by abel]
  exact sub_mem hwx (U.smul_mem _ hy)

include hv hb in
private theorem integral_leading_layer (r : (i : Fin e) → I i → 𝒪[F])
    (hr : ∃ j i, residue 𝒪[F] (r j i) ≠ 0) :
    ∃ j : Fin e, (∀ t : Sigma I, (r t.1 t.2 : F) • v t.1 t.2 ∈ L (j : ℤ)) ∧
      ∑ t : Sigma I, (r t.1 t.2 : F) • v t.1 t.2 ∉ L ((j : ℤ) + 1) := by
  classical
  let s := Finset.univ.filter fun j : Fin e => ∃ i, residue 𝒪[F] (r j i) ≠ 0
  have hs : s.Nonempty := by simpa [s, Finset.Nonempty] using hr
  let j := s.min' hs
  obtain ⟨i₀, hi₀⟩ := (Finset.mem_filter.mp (s.min'_mem hs)).2
  have hl (t : Fin e) (i : I t) : (r t i : F) • v t i ∈ L (t : ℤ) :=
    (L (t : ℤ)).smul_mem (r t i) (hv t i)
  have hn (t : Fin e) (i : I t) (ht : t ≠ j) : (r t i : F) • v t i ∈ L ((j : ℤ) + 1) := by
    by_cases hjt : j < t
    · exact 𝓒.antitone (by exact_mod_cast Nat.succ_le_of_lt (Fin.lt_def.mp hjt)) (hl t i)
    have hr0 : residue 𝒪[F] (r t i) = 0 := by
      by_contra h
      exact hjt (lt_of_le_of_ne (s.min'_le t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, h⟩⟩)) ht.symm)
    have hp : r t i ∈ maximalIdeal 𝒪[F] := (residue_eq_zero_iff _).mp hr0
    apply 𝓒.antitone (show (j : ℤ) + 1 ≤ (t : ℤ) + e by
      have h' : (j : ℤ) < e := by exact_mod_cast j.isLt
      have ht' : (0 : ℤ) ≤ t := by positivity
      omega)
    rw [𝓒.lattice_add_period, ringJacobson_eq_maximalIdeal]
    exact Submodule.smul_mem_smul hp (hv t i)
  refine ⟨j, fun ⟨t, i⟩ => ?_, ?_⟩
  · by_cases ht : t = j
    · subst t
      exact hl j i
    · exact 𝓒.antitone (by omega) (hn t i ht)
  intro h
  have h₁ : ∑ i, (r j i : F) • v j i ∈ L ((j : ℤ) + 1) := by
    rw [Fintype.sum_sigma] at h
    have h₂ : (∑ t ∈ Finset.univ.erase j, ∑ i, (r t i : F) • v t i) ∈ L ((j : ℤ) + 1) :=
      Submodule.sum_mem _ fun t ht => Submodule.sum_mem _ fun i _ => hn t i (Finset.ne_of_mem_erase ht)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at h
    have h₃ := sub_mem h h₂
    simpa only [add_sub_cancel_left] using h₃
  have hsum : ∑ i, residue 𝒪[F] (r j i) • b j i = 0 := by
    have h := (𝓒.intervalMk_eq_iff
      (Submodule.sum_mem _ (fun i _ => hl j i)) (zero_mem (L (j : ℤ)))).mpr
      (show (∑ i, (r j i : F) • v j i) - 0 ∈ L ((j : ℤ) + 1) by simpa only [sub_zero] using h₁)
    rw [intervalMk_sum_smul 𝓒 (r j) (v j) (hv j)] at h
    simp only [hb] at h
    have hz : 𝓒.intervalMk (j : ℤ) ((j : ℤ) + 1) 0 (zero_mem _) = 0 :=
      (𝓒.intervalSubmodule (j : ℤ) ((j : ℤ) + 1)).mkQ.map_zero
    exact h.trans hz
  exact hi₀ (Fintype.linearIndependent_iff.mp (b j).linearIndependent _ hsum i₀)

set_option maxHeartbeats 500000 in
include hv hb hϖ in
/-- Bases of the successive layers of one period lift to a basis, with the lifted vectors
splitting every lattice of the chain. -/
theorem exists_splittingBasis_of_layerLifts : ∃ B : Module.Basis (Sigma I) F V,
    (∀ t : Sigma I, B t = v t.1 t.2) ∧ 𝓒.Splits B := by
  classical
  let w : Sigma I → V := fun t => v t.1 t.2
  have hlead (c : Sigma I → F) (hc : ∃ t, c t ≠ 0) :
      ∃ p : ℤ, (∀ t, c t • w t ∈ L p) ∧ ∑ t, c t • w t ∉ L (p + 1) := by
    obtain ⟨q, r, hr, i, hi⟩ := exists_primitive_coeffs hϖ c hc
    obtain ⟨j, hterms, hsum⟩ := integral_leading_layer 𝓒 b v hv hb (fun j i => r ⟨j, i⟩)
      ⟨i.1, i.2, hi⟩
    refine ⟨(j : ℤ) + e * q, fun t => ?_, ?_⟩
    · rw [hr, mul_smul, 𝓒.zpow_smul_mem_iff hϖ, add_sub_cancel_right]
      exact hterms t
    · have heq : (∑ t, c t • w t) = (ϖ : F) ^ q • ∑ t : Sigma I, (r t : F) • w t := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [hr, mul_smul]
      rw [heq, 𝓒.zpow_smul_mem_iff hϖ, show (j : ℤ) + e * q + 1 - e * q = j + 1 by ring]
      exact hsum
  have hli : LinearIndependent F w := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    by_contra hi
    obtain ⟨p, -, hp⟩ := hlead c ⟨i, hi⟩
    exact hp (hc.symm ▸ zero_mem _)
  let B := Module.Basis.mk hli (layerLifts_span hϖ 𝓒 b v hv hb).ge
  refine ⟨B, fun t => Module.Basis.mk_apply _ _ t, ?_⟩
  intro c i hi t
  simp only [B, Module.Basis.mk_apply] at hi ⊢
  by_cases ht : c t = 0
  · simp [ht]
  obtain ⟨p, hterms, hp⟩ := hlead c ⟨t, ht⟩
  have hip : i ≤ p := le_of_not_gt fun h => hp (𝓒.antitone (by omega) hi)
  exact 𝓒.antitone hip (hterms t)

end LayerBases

include hϖ in
/-- In a splitting basis, testing the image of each vector at its exact weight tests an
endomorphism's filtration degree. -/
theorem mem_endFiltration_iff_splittingBasis {I : Type uI} [Fintype I] (B : Module.Basis I F V)
    (hB : 𝓒.Splits B) (wt : I → ℤ) (hwt : ∀ i, ExactDepth 𝓒 (B i) (wt i))
    {x : Module.End F V} {d : ℤ} :
    x ∈ 𝓒.endFiltration d ↔ ∀ i, x (B i) ∈ L (wt i + d) := by
  refine ⟨fun hx i => hx (wt i) _ (hwt i).1, fun hx j v hv => ?_⟩
  have heq := B.sum_repr v
  have hterms := hB (fun i => B.repr v i) j (heq.symm ▸ hv)
  rw [← heq, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  by_cases h : B.repr v i = 0
  · simp [h]
  have ht := hterms i
  rw [𝓒.smul_mem_iff hϖ h] at ht ⊢
  exact 𝓒.antitone (show j + d - e * ordOf hϖ (B.repr v i) ≤ wt i + d by
    have hi := (hwt i).le 𝓒 ht
    omega) (hx i)

end Langlands.BushnellKutzko.CriticalDerived
