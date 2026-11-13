import Langlands.LocalFactor.DeligneHenniartTopLayerDifferent
import Langlands.LocalField.DVRTraceIdealsProof
import Langlands.LocalField.RelativeIdealPowers
import Langlands.LocalFactor.Ramification.Herbrand.ConvexityProof

/-!
# A trace bound for subextensions of a Galois extension

Let `K ⊆ F ⊆ M` be p-adic fields with `M/K` finite Galois, `G = Gal(M/K)` and
`J = Gal(M/F)`. Write `g_i = |G_i|` and `j_i = |J_i|` for the orders of the lower ramification
groups. If `z ∈ F` has `ord_M(z) > ∫_0^t j_s ds` with `t = ψ_{M/K}(n)`, then
`ord_K(Tr_{F/K} z) ≥ n + 1`. The proof computes the different of `F/K` from Hilbert's formula
for `M/K` and `M/F` and the tower formula for differents, and applies the exact trace image of
ideal powers.
-/

noncomputable section

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer

open IsLocalRing Ramification.Padic PadicField.TopologicalData

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

universe u v w

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p} {F : PadicField.{v} p}
  {M : PadicField.{w} p}
  [Algebra K.Carrier F.Carrier] [Algebra F.Carrier M.Carrier] [Algebra K.Carrier M.Carrier]
  [IsScalarTower K.Carrier F.Carrier M.Carrier]
  [IsScalarTower (Padic p) K.Carrier F.Carrier] [IsScalarTower (Padic p) F.Carrier M.Carrier]
  [IsScalarTower (Padic p) K.Carrier M.Carrier]
  [FiniteDimensional K.Carrier M.Carrier] [IsGalois K.Carrier M.Carrier]
  (TK : K.TopologicalData) (TF : F.TopologicalData) (TM : M.TopologicalData)

/-- The tower formula for differents, in exponents: with `G_N = 1`, the different of
`O_F/O_K` is `m_F ^ d` with `Σ_{i<N} (g_i - 1) = Σ_{i<N} (j_i - 1) + j_0 d`. -/
theorem exists_different_exponent {N : ℕ} (hN : lowerRamificationGroup TM K.Carrier N = ⊥) :
    letI := TK.topology
    letI := TK.valuativeRel
    letI := TK.localField
    letI := TF.topology
    letI := TF.valuativeRel
    letI := TF.localField
    letI := relativeIntegerAlgebra TK TF
    haveI := relativeIntegerAlgebra_isTorsionFree TK TF
    ∃ d : ℕ, differentIdeal TK.Integers TF.Integers = maximalIdeal TF.Integers ^ d ∧
      ∑ i ∈ Finset.range N, (lowerGroupOrder TM K.Carrier i - 1) =
        ∑ i ∈ Finset.range N, (lowerGroupOrder TM F.Carrier i - 1) +
          lowerGroupOrder TM F.Carrier 0 * d := by
  let := TK.topology
  let := TK.valuativeRel
  let := TK.localField
  let := TF.topology
  let := TF.valuativeRel
  let := TF.localField
  let := TM.topology
  let := TM.valuativeRel
  let := TM.localField
  let := relativeIntegerAlgebra TK TF
  let := relativeIntegerAlgebra TF TM
  let := relativeIntegerAlgebra TK TM
  have := relativeIntegerAlgebraTower TK TF TM
  have := relativeIntegerAlgebra_isTorsionFree TK TF
  have := relativeIntegerAlgebra_isTorsionFree TF TM
  have := relativeIntegerAlgebra_isTorsionFree TK TM
  have : FiniteDimensional F.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) F.Carrier M.Carrier
  have : FiniteDimensional K.Carrier F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier F.Carrier
  have : IsGalois F.Carrier M.Carrier := IsGalois.tower_top_of_isGalois K.Carrier F.Carrier M.Carrier
  have hKF := (LocalClassField.NYLL.relativeIntegerStructure p K F TK TF).2
  have hFM := (LocalClassField.NYLL.relativeIntegerStructure p F M TF TM).2
  have hKM := (LocalClassField.NYLL.relativeIntegerStructure p K M TK TM).2
  have : CharZero K.Carrier := Algebra.charZero_of_charZero (Padic p) K.Carrier
  have : CharZero TK.Integers := ⟨fun a b h => Nat.cast_injective (R := K.Carrier)
    (by simpa using congrArg Subtype.val h)⟩
  have : Algebra.IsSeparable (FractionRing TK.Integers) (FractionRing TM.Integers) := by
    have : FiniteDimensional (FractionRing TK.Integers) (FractionRing TM.Integers) :=
      .of_isLocalization TK.Integers TM.Integers (nonZeroDivisors TK.Integers)
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- the different of `O_F/O_K` is a power of `m_F`
  have hne : differentIdeal TK.Integers TF.Integers ≠ ⊥ := by
    have : Algebra.IsSeparable (FractionRing TK.Integers) (FractionRing TF.Integers) := by
      have : FiniteDimensional (FractionRing TK.Integers) (FractionRing TF.Integers) :=
        .of_isLocalization TK.Integers TF.Integers (nonZeroDivisors TK.Integers)
      exact Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact differentIdeal_ne_bot
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible TF.Integers
  obtain ⟨d, hd⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hd' : differentIdeal TK.Integers TF.Integers = maximalIdeal TF.Integers ^ d := by
    rw [hd, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  refine ⟨d, hd', ?_⟩
  have hNF : lowerRamificationGroup TM F.Carrier N = ⊥ := by
    rw [Ramification.HerbrandBridge.lowerRamificationGroup_subfield_eq_comap K.Carrier F.Carrier TM N, hN]
    rw [MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff _).mpr (fun σ τ h => AlgEquiv.ext fun x =>
      congrArg (fun ρ : M.Carrier ≃ₐ[K.Carrier] M.Carrier => ρ x) h)
  have hG := differentIdeal_eq_maximalIdeal_pow TK TM hN
  have hJ := differentIdeal_eq_maximalIdeal_pow TF TM hNF
  have hram : TM.ramificationIndex = lowerGroupOrder TM F.Carrier 0 * TF.ramificationIndex :=
    (lowerGroupOrder_zero_mul_ramificationIndex TF TM).symm
  have hmap := map_maximalIdeal_pow_of_ramificationIndex_eq_mul TF TM _ hram d
  have htower := differentIdeal_eq_differentIdeal_mul_differentIdeal TK.Integers TF.Integers
    TM.Integers
  rw [hG, hJ, hd'] at htower
  change _ = _ * (maximalIdeal TF.Integers ^ d).map (relativeIntegerMap TF TM) at htower
  rw [hmap, ← pow_add] at htower
  have h := congrArg Order.coheight htower
  simpa only [IsDiscreteValuationRing.coheight_pow_maximalIdeal, Nat.cast_inj] using h

omit [IsScalarTower (Padic p) K.Carrier F.Carrier] [FiniteDimensional K.Carrier M.Carrier]
  [IsGalois K.Carrier M.Carrier] in
/-- The lower group orders over `F` are at most those over `K`. -/
theorem lowerGroupOrder_le_of_tower (i : ℕ) :
    lowerGroupOrder TM F.Carrier i ≤ lowerGroupOrder TM K.Carrier i := by
  have h := Ramification.HerbrandBridge.lowerGroupOrder_subfield_mul_relIndex
    K.Carrier F.Carrier TM i
  have hpos := lowerGroupOrder_pos TM K.Carrier i
  rw [← h] at hpos ⊢
  exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left hpos)

/-- `Σ_{i<N} c_i ≥ c_0 + Σ_{i<N} c_{i+1} ramp_i(t)` for `c ≥ 0` with `c_N = 0`. -/
theorem sum_ge_add_rampSum (c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i) (N : ℕ) (hN : c N = 0) (t : ℝ) :
    c 0 + Ramification.HerbrandBridge.rampSum c N t ≤ ∑ i ∈ Finset.range N, c i := by
  have h1 : Ramification.HerbrandBridge.rampSum c N t ≤ ∑ i ∈ Finset.range N, c (i + 1) := by
    unfold Ramification.HerbrandBridge.rampSum
    apply Finset.sum_le_sum
    intro i _
    have h0 := Ramification.Herbrand.ramp_nonneg i t
    have h1 : Ramification.Herbrand.ramp i t ≤ 1 := min_le_left _ _
    nlinarith [hc (i + 1)]
  have h2 : ∑ i ∈ Finset.range (N + 1), c i = c 0 + ∑ i ∈ Finset.range N, c (i + 1) :=
    Finset.sum_range_succ' c N |>.trans (add_comm _ _)
  rw [Finset.sum_range_succ, hN, add_zero] at h2
  linarith

open Ramification.HerbrandBridge in
/-- The trace bound: if `z ∈ F` has `ord_M(z) > ∫_0^t |Gal(M/F)_s| ds` with
`t = ψ_{M/K}(n)`, written as a weighted ramp sum, then `ord_K(Tr_{F/K} z) ≥ n + 1`. -/
theorem trace_mem_additiveLattice (n N : ℕ) (hcut : ramificationCutoff TM K.Carrier ≤ N)
    (htN : herbrandPsi TM K.Carrier n ≤ N) (z : F.Carrier) (hz : z ≠ 0)
    (h : rampSum (fun i => (lowerGroupOrder TM F.Carrier i : ℝ)) N
        (herbrandPsi TM K.Carrier n) < TM.ord (algebraMap F.Carrier M.Carrier z)) :
    Algebra.trace K.Carrier F.Carrier z ∈ TK.additiveLattice (-((n : ℤ) + 1)) := by
  let TF : F.TopologicalData := F.canonicalTopologicalData
  set t := herbrandPsi TM K.Carrier n with ht
  set g : ℕ → ℕ := fun i => lowerGroupOrder TM K.Carrier i with hg
  set j : ℕ → ℕ := fun i => lowerGroupOrder TM F.Carrier i with hj
  have hN : lowerRamificationGroup TM K.Carrier N = ⊥ :=
    lowerRamificationGroup_eq_bot_of_cutoff TM K.Carrier N hcut
  have hNF : lowerRamificationGroup TM F.Carrier N = ⊥ := by
    rw [Ramification.HerbrandBridge.lowerRamificationGroup_subfield_eq_comap K.Carrier F.Carrier
      TM N, hN, MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff _).mpr (fun σ τ h => AlgEquiv.ext fun x =>
      congrArg (fun ρ : M.Carrier ≃ₐ[K.Carrier] M.Carrier => ρ x) h)
  have hgN : g N = 1 := by
    simp only [hg, lowerGroupOrder, hN, Subgroup.mem_bot, Nat.card_unique]
  have hjN : j N = 1 := by
    simp only [hj, lowerGroupOrder, hNF, Subgroup.mem_bot, Nat.card_unique]
  have : FiniteDimensional F.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) F.Carrier M.Carrier
  have : FiniteDimensional K.Carrier F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier F.Carrier
  have : IsGalois F.Carrier M.Carrier := IsGalois.tower_top_of_isGalois K.Carrier F.Carrier M.Carrier
  -- ramification indices
  have hKM := lowerGroupOrder_zero_mul_ramificationIndex TK TM
  have hFM := lowerGroupOrder_zero_mul_ramificationIndex TF TM
  have heKpos := TK.ramificationIndex_pos
  have hπ := ramificationIndex_mul_ord_algebraMap TK TF TK.uniformizer
  rw [TK.ord_uniformizer, mul_one] at hπ
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = TF.ord (algebraMap K.Carrier F.Carrier TK.uniformizer) := by
    refine ⟨_, Int.toNat_of_nonneg ?_⟩
    have : (0 : ℤ) < TK.ramificationIndex := by exact_mod_cast heKpos
    have : (0 : ℤ) ≤ TF.ramificationIndex := by positivity
    nlinarith
  have hKF : TF.ramificationIndex = e * TK.ramificationIndex := by
    have : ((TF.ramificationIndex : ℕ) : ℤ) = ((e * TK.ramificationIndex : ℕ) : ℤ) := by
      push_cast
      rw [he]
      linarith
    exact_mod_cast this
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, zero_mul] at hKF
      exact absurd hKF (TF.ramificationIndex_pos.ne')
    · exact h0
  have hg0 : g 0 = j 0 * e := by
    apply Nat.eq_of_mul_eq_mul_right heKpos
    rw [mul_assoc, ← hKF]
    exact hKM.trans hFM.symm
  -- the different exponent
  obtain ⟨d, hd, hsum⟩ := exists_different_exponent TK TF TM hN
  -- the order of `z`
  have hzM : algebraMap F.Carrier M.Carrier z ≠ 0 := (map_ne_zero _).mpr hz
  have hordz := ord_algebraMap_eq TF TM z
  have hR0 : 0 ≤ rampSum (fun i => (lowerGroupOrder TM F.Carrier i : ℝ)) N t := by
    unfold rampSum
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
      (Ramification.Herbrand.ramp_nonneg i t)
  have hj0pos : 0 < j 0 := lowerGroupOrder_pos TM F.Carrier 0
  have hzF : 0 < TF.ord z := by
    have h1 : (0 : ℝ) < TM.ord (algebraMap F.Carrier M.Carrier z) := hR0.trans_lt h
    have h2 : (0 : ℤ) < TM.ord (algebraMap F.Carrier M.Carrier z) := by exact_mod_cast h1
    rw [hordz] at h2
    exact pos_of_mul_pos_right h2 (by positivity)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = TF.ord z := ⟨_, Int.toNat_of_nonneg hzF.le⟩
  -- the arithmetic
  have hphi : herbrandPhi TM K.Carrier t = n := herbrandPhi_herbrandPsi TM K.Carrier n
  have ht0 : 0 ≤ t := by
    rw [ht]
    have := (herbrandPsi_strictMono TM K.Carrier).monotone (Nat.cast_nonneg (α := ℝ) n)
    simpa using this
  rw [herbrandPhi_eq_sum TM K.Carrier hcut ht0 htN] at hphi
  have hg0pos : (0 : ℝ) < g 0 := by exact_mod_cast lowerGroupOrder_pos TM K.Carrier 0
  have hRg : rampSum (fun i => (g i : ℝ)) N t = g 0 * n := by
    rw [div_eq_iff hg0pos.ne'] at hphi
    simpa [hg, mul_comm] using hphi
  have hineq := sum_ge_add_rampSum (fun i => (g i : ℝ) - j i)
    (fun i => sub_nonneg.mpr (by exact_mod_cast lowerGroupOrder_le_of_tower TM i)) N
    (by simp [hgN, hjN]) t
  have hrs : rampSum (fun i => (g i : ℝ) - j i) N t =
      rampSum (fun i => (g i : ℝ)) N t - rampSum (fun i => (j i : ℝ)) N t := by
    unfold rampSum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsumR : (∑ i ∈ Finset.range N, ((g i : ℝ) - j i)) = (j 0 : ℝ) * d := by
    have hcast : ((∑ i ∈ Finset.range N, (g i - 1) : ℕ) : ℝ) =
        ((∑ i ∈ Finset.range N, (j i - 1) + j 0 * d : ℕ) : ℝ) := by
      exact_mod_cast hsum
    have hgc : ∀ i, ((g i - 1 : ℕ) : ℝ) = (g i : ℝ) - 1 := fun i => by
      rw [Nat.cast_sub (lowerGroupOrder_one_le TM K.Carrier i), Nat.cast_one]
    have hjc : ∀ i, ((j i - 1 : ℕ) : ℝ) = (j i : ℝ) - 1 := fun i => by
      rw [Nat.cast_sub (lowerGroupOrder_one_le TM F.Carrier i), Nat.cast_one]
    simp only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, hgc, hjc, Finset.sum_sub_distrib] at hcast
    rw [Finset.sum_sub_distrib]
    linarith
  have hzR : (j 0 : ℝ) * a = TM.ord (algebraMap F.Carrier M.Carrier z) := by
    rw [hordz, ← ha]
    push_cast
    rfl
  have hkey : (j 0 : ℝ) * (e * (n + 1) - 1) < j 0 * (d + a) := by
    have hg0' : (g 0 : ℝ) = j 0 * e := by exact_mod_cast hg0
    rw [hrs, hRg, hsumR] at hineq
    simp only [hg, hj] at hineq h ⊢
    nlinarith
  have hkey' : e * (n + 1) ≤ d + a := by
    have hj0R : (0 : ℝ) < j 0 := by exact_mod_cast hj0pos
    have := lt_of_mul_lt_mul_left hkey hj0R.le
    have : ((e * (n + 1) : ℕ) : ℝ) < ((d + a + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := (Nat.cast_lt (α := ℝ)).mp this
    omega
  have hr : n + 1 ≤ (d + a) / e := (Nat.le_div_iff_mul_le hepos).mpr (by linarith [hkey'])
  -- the trace image
  let := TK.topology
  let := TK.valuativeRel
  let := TK.localField
  let := TF.topology
  let := TF.valuativeRel
  let := TF.localField
  let := relativeIntegerAlgebra TK TF
  let := relativeIntegerFieldAlgebra (E := F) TK
  have := relativeIntegerFieldTower (E := F) TK
  have := relativeIntegerTower TK TF
  obtain ⟨hclosure, hmodule⟩ := LocalClassField.NYLL.relativeIntegerStructure p K F TK TF
  have : CharZero K.Carrier := Algebra.charZero_of_charZero (Padic p) K.Carrier
  have : Algebra.IsSeparable K.Carrier F.Carrier := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hmap := map_maximalIdeal_algebraMap_of_ramificationIndex_eq_mul TK TF e hKF
  have hzint : z ∈ TF.Integers := (TF.mem_integers_iff_zero_le_ord hz).mpr hzF.le
  have hzmem : (⟨z, hzint⟩ : TF.Integers) ∈ maximalIdeal TF.Integers ^ a := by
    rw [TF.mem_maximalIdeal_pow_iff_ord TF.uniformizer TF.ord_uniformizer]
    exact Or.inr ha.le
  obtain ⟨c, hc, hcz⟩ := (LocalField.dvrTraceIdeals TK.Integers TF.Integers K.Carrier F.Carrier e d
    hepos hmap hd a (Algebra.trace K.Carrier F.Carrier z)).mp ⟨⟨z, hzint⟩, hzmem, rfl⟩
  rw [← hcz]
  by_cases hc0 : (c : K.Carrier) = 0
  · change (algebraMap TK.Integers K.Carrier c) ∈ _
    change (c : K.Carrier) ∈ _
    rw [hc0]
    exact zero_mem _
  have hcord := (TK.mem_maximalIdeal_pow_iff_ord TK.uniformizer TK.ord_uniformizer _ c).mp hc
  have hle : ((n : ℤ) + 1) ≤ TK.ord (c : K.Carrier) := by
    rcases hcord with h0 | h0
    · exact absurd h0 hc0
    · have : ((n : ℤ) + 1) ≤ (((d + a) / e : ℕ) : ℤ) := by exact_mod_cast hr
      linarith
  exact mem_additiveLattice_neg_of_le_ord TK hle hc0

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer
