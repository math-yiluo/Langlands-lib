import Langlands.BushnellKutzko.PureStratumApproximationChainImprovement
import Langlands.BushnellKutzko.PureStratumApproximationNonsplitTransfer

/-! # The final step of the proof of BK93 (2.4.1)(i)

BK93, printed pp. 70–71: if the derived stratum of `β − γ` is fundamental and not split, then
(2.3.4) over `E = F[γ]` gives a simple stratum `[𝔅',ρ,ρ−1,c]` over `E` containing the derived
coset, on a finer chain at the same normalized level. The refinement theorem (2.2.8) then
approximates `β` by a simple stratum one step deeper whose generated field has the ramification
index and residue degree of `F[γ,c]` (it need not equal `F[γ,c]`). If `c ∈ E` this is an
approximation of smaller normalized depth with the invariants of `F[γ]`; otherwise the degree of
the approximating field, the product of these invariants, is `[F[γ,c]:F] > [F[γ]:F]`, and
`k₀ = −ρ`.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uE uV

section Sandwich

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

omit [ValuativeRel F] in
theorem sub_le_of_strictMono {σ : ℤ → ℤ} (hσ : StrictMono σ) {i j : ℤ} (h : i ≤ j) :
    j - i ≤ σ j - σ i := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
  have hj : j = i + k := by omega
  subst hj
  clear hk h
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := hσ (show i + (k : ℤ) < i + ((k + 1 : ℕ) : ℤ) by push_cast; omega)
    push_cast at h1 ih ⊢
    omega

/-- If every lattice of `𝓛` is a lattice of `𝓜`, then every lattice of `𝓜` is sandwiched
between two consecutive lattices of `𝓛`. -/
theorem sandwiched_of_lattice_mem (𝓛 𝓜 : LatticeChain 𝒪[F] F V)
    (h : ∀ i, ∃ j, (𝓛.lattice i : Set V) = 𝓜.lattice j) :
    ∀ t, ∃ q, 𝓛.lattice (q + 1) ≤ 𝓜.lattice t ∧ 𝓜.lattice t ≤ 𝓛.lattice q := by
  classical
  choose σ hσ using h
  have hσ' : ∀ i, 𝓛.lattice i = 𝓜.lattice (σ i) := fun i => SetLike.coe_injective (hσ i)
  have hmono : StrictMono σ := by
    intro i j hij
    have h1 := 𝓛.strictAnti hij
    rw [hσ' i, hσ' j] at h1
    exact 𝓜.strictAnti.lt_iff_gt.mp h1
  intro t
  let P : ℤ → Prop := fun i => σ i ≤ t
  have hbdd : ∃ b, ∀ i, P i → i ≤ b := by
    refine ⟨|t - σ 0|, fun i hi => ?_⟩
    simp only [P] at hi
    have habs := le_abs_self (t - σ 0)
    have habs' := abs_nonneg (t - σ 0)
    rcases le_or_gt 0 i with h0 | h0
    · have := sub_le_of_strictMono hmono h0
      omega
    · omega
  have hne : ∃ i, P i := by
    have habs := le_abs_self (t - σ 0)
    have habs' := abs_nonneg (t - σ 0)
    refine ⟨t - σ 0 - 1 - |t - σ 0|, ?_⟩
    have h2 := sub_le_of_strictMono hmono (show t - σ 0 - 1 - |t - σ 0| ≤ 0 by omega)
    simp only [P]
    omega
  obtain ⟨q, hq, hqmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨q, ?_, ?_⟩
  · rw [hσ' (q + 1)]
    apply 𝓜.antitone
    by_contra hlt
    exact absurd (hqmax (q + 1) (by simp only [P]; omega)) (by omega)
  · rw [hσ' q]
    exact 𝓜.antitone hq

end Sandwich

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

/-- **The final step of the proof of BK93 (2.4.1)(i)**, printed pp. 70–71, given (2.3.4) for
`E`. Let `S` be simple with `E = F[S.b]` and let the derived stratum `D` of `β − S.b` be
fundamental and not split. Then either `β` has a simple approximation of strictly smaller
normalized depth with the invariants of `F[S.b]`, or there are simple strata `T`, `U` on a common
chain with `U` one step deeper, both approximating `β`, with `k₀(U.b) = −T.r`, with `F[U.b]` of
strictly larger degree than `F[S.b]`, and with the invariants of `F[T.b]` dividing those of
`F[U.b]`. -/
theorem improvement_or_increase (hRef : NonsplitRefinementPremise.{uE, uV})
    (β : Module.End F V) (S : Stratum 𝒪[F] F V) (s : TameCorestriction 𝒪[F] F E V)
    (D : Stratum (subfieldIntegers F E) E V) (hD : S.IsDerivedStratum E (β - S.b) s D)
    (hfund : D.IsFundamental) (hns : ¬ D.IsSplit) :
    (∃ T : Stratum 𝒪[F] F V, T.IsSimple ∧ β ∈ T.coset ∧
      T.r * S.chain.period < S.r * T.chain.period ∧
      elementRamificationIndex F T.b = elementRamificationIndex F S.b ∧
      elementResidueDegree F T.b = elementResidueDegree F S.b) ∨
    (∃ T U : Stratum 𝒪[F] F V, U.chain = T.chain ∧ U.n = T.n ∧ U.r = T.r - 1 ∧
      T.IsSimple ∧ β ∈ T.coset ∧ U.IsSimple ∧ β ∈ U.coset ∧
      criticalExponent U.chain U.b = ((-T.r : ℤ) : WithBot ℤ) ∧
      elementDegree F S.b < elementDegree F U.b ∧
      elementRamificationIndex F T.b ∣ elementRamificationIndex F U.b ∧
      elementResidueDegree F T.b ∣ elementResidueDegree F U.b) := by
  classical
  obtain ⟨hS, ⟨βE, hβES, hβE⟩, hb, hDlat, hDn, hDr, hDb⟩ := hD
  have := S.chain.finiteDimensional
  have : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
  have hE := normalized_of_generated S hS.1 hβES hβE
  obtain ⟨C, hC, hCr, hcos, hslope, hlat⟩ := exists_simple_of_not_isSplit hRef D hfund hns
  let 𝓜 := liftChain C.chain
  have hM : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓜.stabilizer := liftChain_normalized C.chain
  have hClat : ∀ i, (C.chain.lattice i : Set V) = 𝓜.lattice i := fun i => rfl
  have hsw := sandwiched_of_lattice_mem S.chain 𝓜 (fun i => by
    obtain ⟨j, hj⟩ := hlat i
    exact ⟨j, (hDlat i).symm.trans hj⟩)
  set ρ := C.n with hρ_def
  -- periods
  have hpD : S.chain.period = subfieldRamificationIndex F E * D.chain.period := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    rw [← liftChain_period D.chain]
    exact period_eq_of_coe_lattice_eq S.chain (liftChain D.chain)
      (fun i => (hDlat i).symm) hπ hπ rfl
  have hρ : ρ * S.chain.period = S.r * 𝓜.period := by
    change ρ * (S.chain.period : ℤ) = S.r * ((liftChain C.chain).period : ℤ)
    rw [liftChain_period, hpD, ← hDn]
    push_cast
    rw [show ρ * (subfieldRamificationIndex F E * (D.chain.period : ℤ)) =
      subfieldRamificationIndex F E * (C.n * D.chain.period) by rw [hρ_def]; ring, ← hslope]
    ring
  have hDself : D.b ∈ D.coset := by
    show D.b - D.b ∈ D.chain.endFiltration (-D.r)
    rw [sub_self]
    exact zero_mem _
  have hsC : s (β - S.b) ∈ C.coset := by
    rw [← hDb]
    exact hcos hDself
  have hQ : ∀ y : Module.End E V, y.restrictScalars F ∈ S.chain.endFiltration (1 - S.r) →
      y.restrictScalars F ∈ 𝓜.endFiltration (1 - ρ) := by
    intro y hy
    have hy' : y ∈ D.chain.endFiltration (-D.r) := by
      rw [hDr, show -(S.r - 1) = 1 - S.r by ring]
      exact (mem_endFiltration_restrictScalars hDlat).mpr hy
    have h1 : D.b + y - C.b ∈ C.chain.endFiltration (-C.r) := hcos (by
      show D.b + y - D.b ∈ D.chain.endFiltration (-D.r)
      rwa [add_sub_cancel_left])
    have h2 : D.b - C.b ∈ C.chain.endFiltration (-C.r) := hcos hDself
    have h3 := sub_mem h1 h2
    rw [sub_sub_sub_cancel_right, add_sub_cancel_left, hCr,
      show -(C.n - 1) = 1 - ρ by rw [hρ_def]; ring] at h3
    exact (mem_endFiltration_restrictScalars hClat).mp h3
  obtain ⟨T, U, hTc, hUc, hUn, hTr, hUr, hT, hβT, hU, hβU, heT, hfT, heU, hfU, hkU⟩ :=
    exists_refinement_of_coset S hS hβES hβE s hb 𝓜 hM hsw hρ C hClat rfl hCr hC hsC hQ
  have hpos : (0 : ℤ) < S.chain.period := by exact_mod_cast S.chain.period_pos
  by_cases hcE : ∃ e : E, C.b = algebraMap E (Module.End E V) e
  · -- `c ∈ E`: an approximation of smaller normalized depth
    left
    obtain ⟨e, he⟩ := hcE
    have hpair : Algebra.adjoin F ({S.b, C.b.restrictScalars F} : Set (Module.End F V)) =
        elementAlgebra S.b := by
      rw [he, restrictScalars_algebraMap]
      exact adjoin_pair_eq_elementAlgebra (subfieldEmbedding_mem_elementAlgebra hβES hβE e)
    rw [hpair] at heU hfU
    refine ⟨U, hU, hβU, ?_, heU, hfU⟩
    rw [hUr, hUc]
    linarith
  · -- `c ∉ E`: the degree increases
    right
    have hrange : elementAlgebra S.b = (subfieldEmbedding F E V).range := by
      change Algebra.adjoin F ({S.b} : Set (Module.End F V)) = _
      rw [← hβES, ← AlgHom.map_adjoin_singleton (subfieldEmbedding F E V) βE, hβE,
        Algebra.map_top]
    have hcF : C.b.restrictScalars F ∉ elementAlgebra S.b := by
      intro h
      rw [hrange] at h
      obtain ⟨e, he⟩ := h
      apply hcE
      refine ⟨e, LinearMap.restrictScalars_injective F ?_⟩
      rw [restrictScalars_algebraMap]
      exact he.symm
    -- the critical exponent of `c` is `−ρ`
    obtain ⟨⟨hCf, hCn'⟩, hCv⟩ := hC.1
    have hCbot : elementAlgebra C.b ≠ ⊥ := by
      intro h
      have hmem : C.b ∈ (⊥ : Subalgebra E (Module.End E V)) :=
        h ▸ Algebra.self_mem_adjoin_singleton E C.b
      obtain ⟨e, he⟩ := Algebra.mem_bot.mp hmem
      exact hcE ⟨e, he.symm⟩
    have hCmem : C.b ∈ C.chain.endFiltration (-ρ) := by
      apply mem_endFiltration_of_le_valuation_subfield C.chain
      rw [hCv]
      exact_mod_cast le_rfl
    have hcrit := derived_mem_criticalIndexSet_of_mem C.chain C.b hCf hCn' hCbot hCmem
    obtain ⟨k₁, hk₁, hk₁e⟩ := derived_exists_isGreatest_criticalIndexSet C.chain C.b hCf hCn' hCbot
    have hk₁le : -ρ ≤ k₁ := hk₁.2 hcrit
    have hk₁lt : k₁ < -C.r := by
      have h := hC.2
      rw [hk₁e] at h
      exact WithBot.coe_lt_coe.mp h
    have hkc : criticalExponent C.chain C.b = ((-ρ : ℤ) : WithBot ℤ) := by
      rw [hk₁e]
      congr 1
      rw [hCr] at hk₁lt
      omega
    have hkS : criticalExponent 𝓜 S.b < ((-ρ : ℤ) : WithBot ℤ) := by
      have hk : criticalExponent S.chain (subfieldEmbedding F E V βE) <
          ((-S.r : ℤ) : WithBot ℤ) := by
        rw [hβES]
        exact hS.2
      rw [← hβES]
      exact criticalExponent_lt_of_normalized S.chain 𝓜 hE hM hβE hk hρ.le
    -- the field `E₁ = F[β,c]`
    set E₁ := Algebra.adjoin F ({S.b, C.b.restrictScalars F} : Set (Module.End F V)) with hE₁
    obtain ⟨⟨hUf, -⟩, -⟩ := hU.1
    have hE₁f : IsField E₁ := by
      by_contra hnf
      have h0 : subalgebraRamificationIndex F E₁ = 0 := by
        unfold subalgebraRamificationIndex
        rw [dite_eq_right hnf]
      have hpos' : 0 < elementRamificationIndex F U.b := by
        unfold elementRamificationIndex
        rw [dite_eq_left hUf]
        let := hUf.toField
        exact subfieldRamificationIndex_pos'
      omega
    have hle : elementAlgebra S.b ≤ E₁ :=
      Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
    have hcE₁ : C.b.restrictScalars F ∈ E₁ :=
      Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hlt : elementAlgebra S.b < E₁ := lt_of_le_of_ne hle (fun h => hcF (h ▸ hcE₁))
    obtain ⟨⟨hSf, -⟩, -⟩ := hS.1
    have hdegU : elementDegree F U.b = Module.finrank F E₁ := by
      rw [← elementRamificationIndex_mul_residueDegree U.b hUf, heU, hfU]
      unfold subalgebraRamificationIndex subalgebraResidueDegree
      rw [dite_eq_left hE₁f, dite_eq_left hE₁f]
      let := hE₁f.toField
      exact subfieldRamificationIndex_mul_residueDegree F E₁
    have hdeg : elementDegree F S.b < elementDegree F U.b := by
      rw [hdegU]
      exact Submodule.finrank_lt_finrank_of_lt
        (show Subalgebra.toSubmodule (elementAlgebra S.b) < Subalgebra.toSubmodule E₁ from hlt)
    let := hSf.toField
    let := hE₁f.toField
    have hdiv : subfieldRamificationIndex F (elementAlgebra S.b) ∣
          subfieldRamificationIndex F E₁ ∧
        subfieldResidueDegree F (elementAlgebra S.b) ∣ subfieldResidueDegree F E₁ :=
      subfieldInvariantsEmbedding (Subalgebra.inclusion hle)
    refine ⟨T, U, by rw [hUc, hTc], hUn, by rw [hUr, hTr], hT, hβT, hU, hβU, ?_, hdeg, ?_, ?_⟩
    · rw [hkU, hkc, hTr]
      exact max_eq_right hkS.le
    · rw [heT, heU]
      unfold elementRamificationIndex subalgebraRamificationIndex
      rw [dite_eq_left hSf, dite_eq_left hE₁f]
      exact hdiv.1
    · rw [hfT, hfU]
      unfold elementResidueDegree subalgebraResidueDegree
      rw [dite_eq_left hSf, dite_eq_left hE₁f]
      exact hdiv.2

end Langlands.BushnellKutzko.PureApproximation
