import Langlands.BushnellKutzko.PureStratumApproximationSlope
import Langlands.BushnellKutzko.PureStratumApproximationBoundedApproximation
import Langlands.BushnellKutzko.NormalizedLevelExistenceProof
import Langlands.BushnellKutzko.StratumApproximationReduction

/-! # Bounds for candidate approximations of a pure stratum -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uV

/-- Periods are bounded by the dimension, and the normalized depths `T.r / e(T)` of pure strata
`T` whose coset contains the element of a pure stratum `S`, with generated algebra of smaller
degree, are bounded below uniformly. -/
def CandidateDepthBoundStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
    (∀ 𝓛 : LatticeChain 𝒪[F] F V, 𝓛.period ≤ Module.finrank F V) ∧
    ∀ S : Stratum 𝒪[F] F V, S.IsPure → ∃ m : ℤ, ∀ T : Stratum 𝒪[F] F V, T.IsPure →
      S.b ∈ T.coset → elementDegree F T.b < elementDegree F S.b → m * T.chain.period ≤ T.r

section Bounds

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- The period of a lattice chain is at most the dimension. -/
theorem period_le_finrank (𝓛 : LatticeChain 𝒪[F] F V) : 𝓛.period ≤ Module.finrank F V := by
  let f : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := (Module.finBasis F V).equivFun
  have hp : (𝓛.linearEquivMap f).period = 𝓛.period := by
    symm
    apply (𝓛.linearEquivMap f).period_unique
    intro i
    change ((𝓛.lattice (i + 𝓛.period)).map _) = Ring.jacobson 𝒪[F] • ((𝓛.lattice i).map
      (f.toLinearMap.restrictScalars 𝒪[F]))
    rw [𝓛.lattice_add_period, Submodule.map_smul'']
  have h := (𝓛.linearEquivMap f).period_le_card
  rwa [hp, Fintype.card_fin] at h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
/-- A nonzero scalar multiple generates the same algebra. -/
theorem elementAlgebra_smul {c : F} (hc : c ≠ 0) (x : Module.End F V) :
    elementAlgebra (c • x) = elementAlgebra x := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rw [Set.singleton_subset_iff]
    exact Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton F x) c
  · apply Algebra.adjoin_le
    rw [Set.singleton_subset_iff]
    have h := Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton F (c • x)) c⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
theorem elementDegree_smul {c : F} (hc : c ≠ 0) (x : Module.End F V) :
    elementDegree F (c • x) = elementDegree F x := by
  unfold elementDegree
  rw [elementAlgebra_smul hc]

omit [FiniteDimensional F V] in
/-- An element of valuation at least `k` lies in `𝔓^k`. -/
theorem mem_endFiltration_of_le_valuation (A : LatticeChain 𝒪[F] F V) {x : Module.End F V}
    {k : ℤ} (h : (k : WithTop ℤ) ≤ A.valuation x) : x ∈ A.endFiltration k := by
  by_cases hx : x = 0
  · rw [hx]
    exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨s, hs, hs'⟩ := exists_depth A hπ hx
  rw [A.valuation_eq_of_mem_of_notMem hs hs'] at h
  exact A.endFiltration_antitone (WithTop.coe_le_coe.mp h) hs

/-- The uniform lower bound for normalized depths of candidates. -/
theorem candidateDepthBound_aux (S : Stratum 𝒪[F] F V) (hS : S.IsPure) :
    ∃ m : ℤ, ∀ T : Stratum 𝒪[F] F V, T.IsPure → S.b ∈ T.coset →
      elementDegree F T.b < elementDegree F S.b → m * T.chain.period ≤ T.r := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hπ0 : (π : F) ≠ 0 := coe_uniformizer_ne_zero hπ
  set a : ℤ := |S.n| with ha
  set c : F := (π : F) ^ a with hc
  have hc0 : c ≠ 0 := zpow_ne_zero _ hπ0
  have hfield : IsField (elementAlgebra (c • S.b)) := by
    rw [elementAlgebra_smul hc0]
    exact hS.1.1
  obtain ⟨M, hM⟩ := boundedApproximation_aux (c • S.b) hfield hπ
  refine ⟨a - M - 1, fun T hT hβ hdeg => ?_⟩
  set e : ℤ := (T.chain.period : ℤ) with he
  have he0 : 0 < e := by rw [he]; exact_mod_cast T.chain.period_pos
  have heS : (1 : ℤ) ≤ S.chain.period := by exact_mod_cast S.chain.period_pos
  have hself : S.b ∈ S.coset := by
    show S.b - S.b ∈ S.chain.endFiltration (-S.r)
    rw [sub_self]
    exact zero_mem _
  have hslope := pureCosetSlope F V S T hS hT S.b hself hβ
  have ha0 : 0 ≤ a := abs_nonneg _
  have hSa : S.n ≤ a := le_abs_self _
  have hTn : T.n ≤ a * e := by
    by_cases hpos : 0 < T.n
    · have h1 : T.n ≤ T.n * S.chain.period := by nlinarith
      have h2 : S.n * e ≤ a * e := by nlinarith
      rw [← hslope] at h1
      linarith
    · have hpos' := not_lt.mp hpos
      nlinarith
  -- Both elements lie in `𝔓^{−n_T}`, so their multiples by `π^a` lie in the order.
  have hTb : T.b ∈ T.chain.endFiltration (-T.n) := by
    apply mem_endFiltration_of_le_valuation
    exact_mod_cast T.valuation_ge
  have hdiff : S.b - T.b ∈ T.chain.endFiltration (-T.r) := hβ
  have hrn := T.r_lt_n
  have hSb : S.b ∈ T.chain.endFiltration (-T.n) := by
    have h := add_mem hTb (T.chain.endFiltration_antitone (show -T.n ≤ -T.r by omega) hdiff)
    simpa using h
  have hscale {x : Module.End F V} (hx : x ∈ T.chain.endFiltration (-T.n)) :
      c • x ∈ T.chain.endFiltration 0 := by
    have h := (zpow_smul_mem_endFiltration_iff T.chain hπ a (-T.n) x).mpr hx
    exact T.chain.endFiltration_antitone (show (0 : ℤ) ≤ -T.n + e * a by nlinarith) h
  -- The largest integer `t` with `t e ≤ a e − r_T`.
  set t : ℤ := (a * e - T.r) / e with ht
  have hdm := Int.emod_add_mul_ediv (a * e - T.r) e
  have hm0 := Int.emod_nonneg (a * e - T.r) (ne_of_gt he0)
  have hm1 := Int.emod_lt_of_pos (a * e - T.r) he0
  have hmem : ((π : F) ^ (-t)) • (c • S.b - c • T.b) ∈ T.chain.endFiltration 0 := by
    rw [← smul_sub, smul_smul, hc, ← zpow_add₀ hπ0]
    have h := (zpow_smul_mem_endFiltration_iff T.chain hπ (-t + a) (-T.r) (S.b - T.b)).mpr hdiff
    exact T.chain.endFiltration_antitone (show (0 : ℤ) ≤ -T.r + e * (-t + a) by nlinarith) h
  have hdeg' : elementDegree F (c • T.b) < elementDegree F (c • S.b) := by
    rw [elementDegree_smul hc0, elementDegree_smul hc0]
    exact hdeg
  have htM := hM T.chain (c • T.b) t (hscale hSb) (hscale hTb) hdeg' hmem
  have hprod : e * t ≤ e * M := mul_le_mul_of_nonneg_left htM he0.le
  nlinarith

/-- The bounds for candidate approximations. -/
theorem candidateDepthBound : CandidateDepthBoundStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _
  exact ⟨period_le_finrank, candidateDepthBound_aux⟩

end Bounds

end Langlands.BushnellKutzko.PureApproximation
