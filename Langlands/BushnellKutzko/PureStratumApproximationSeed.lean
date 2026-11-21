import Langlands.BushnellKutzko.PureStratumApproximationMaximalReflection
import Langlands.BushnellKutzko.PureStratumApproximationLineChains
import Langlands.BushnellKutzko.PureStratumApproximationTranslation
import Langlands.BushnellKutzko.FundamentalStratum

/-! # A first nonmaximal approximation (BK93 (2.4.3)) from (2.3.11) and (2.3.4) -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uV

/-- BK93 (2.3.11), printed p. 60, as a premise: the top stratum of a pure stratum is nonsplit
fundamental. This is the content of statement (2) of Task 8149. -/
def TopNonsplitPremise : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S : Stratum 𝒪[F] F V), S.IsPure →
      (⟨S.chain, S.n, S.n - 1, S.b, by omega, S.valuation_ge⟩ : Stratum 𝒪[F] F V).IsNonsplit

/-- BK93 (2.3.4), printed p. 58, as a premise: a nonsplit fundamental stratum is contained in
a simple top stratum on a finer chain with the same normalized level. This is the content of
statement (1) of Task 8149. -/
def NonsplitRefinementPremise : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S : Stratum 𝒪[F] F V), S.IsNonsplit →
      ∃ T : Stratum 𝒪[F] F V, T.IsSimple ∧ T.r = T.n - 1 ∧ S.coset ⊆ T.coset ∧
        S.n * T.chain.period = T.n * S.chain.period ∧
        ∀ i, ∃ j, S.chain.lattice i = T.chain.lattice j

/-- BK93 (2.4.3), printed p. 67, for the critical full-degree case: given (2.3.11) and (2.3.4),
some simple stratum whose coset contains `β` generates an algebra of smaller degree. -/
def CandidateSeedStatement : Prop :=
  TopNonsplitPremise.{uF, uV} → NonsplitRefinementPremise.{uF, uV} →
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S : Stratum 𝒪[F] F V), S.IsPure →
    criticalExponent S.chain S.b = ((-S.r : ℤ) : WithBot ℤ) →
    elementDegree F S.b = Module.finrank F V →
    ∃ T : Stratum 𝒪[F] F V,
      T.IsSimple ∧ S.b ∈ T.coset ∧ elementDegree F T.b < elementDegree F S.b

section Helpers

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

/-- Membership in `𝔓^k` bounds the valuation below by `k`. -/
theorem le_valuation_of_mem (A : LatticeChain 𝒪[F] F V) {x : Module.End F V} {k : ℤ}
    (hx : x ∈ A.endFiltration k) : (k : WithTop ℤ) ≤ A.valuation x := by
  by_cases h0 : x = 0
  · rw [h0, A.valuation_zero]
    exact le_top
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨s, hs, hs'⟩ := exists_depth A hπ h0
  rw [A.valuation_eq_of_mem_of_notMem hs hs']
  apply WithTop.coe_le_coe.mpr
  by_contra! hlt
  exact hs' (A.endFiltration_antitone (show s + 1 ≤ k by omega) hx)

variable [FiniteDimensional F V]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The degree of a generated field is at most the dimension. -/
theorem elementDegree_le_finrank (b : Module.End F V) (hf : IsField (elementAlgebra b))
    [Nontrivial V] : elementDegree F b ≤ Module.finrank F V := by
  let : Field (elementAlgebra b) := hf.toField
  let : Module.Finite (elementAlgebra b) V := Module.Finite.of_restrictScalars_finite F _ V
  change Module.finrank F (elementAlgebra b) ≤ _
  rw [← Module.finrank_mul_finrank F (elementAlgebra b) V]
  exact Nat.le_mul_of_pos_right _ Module.finrank_pos

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A generated field of full degree makes `V` a line over it. -/
theorem exists_line_generator (b : Module.End F V) (hf : IsField (elementAlgebra b))
    (h : elementDegree F b = Module.finrank F V) :
    letI := hf.toField
    ∃ v : V, v ≠ 0 ∧ ∀ x : V, ∃ a : elementAlgebra b, a • v = x := by
  let : Field (elementAlgebra b) := hf.toField
  let : Module.Finite (elementAlgebra b) V := Module.Finite.of_restrictScalars_finite F _ V
  have ht := Module.finrank_mul_finrank F (elementAlgebra b) V
  change Module.finrank F (elementAlgebra b) = _ at h
  rw [h] at ht
  have hp : 0 < Module.finrank F V := by
    rw [← h]
    exact Module.finrank_pos
  have h1 : Module.finrank (elementAlgebra b) V = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hp
    rw [mul_one]
    exact ht
  exact finrank_eq_one_iff'.mp h1

end Helpers

/-- Refine the top stratum and show that a full-degree refinement would make the original
stratum simple at depth `n − 1`. -/
theorem candidateSeed : CandidateSeedStatement.{uF, uV} := by
  intro hTop hRef F _ _ _ _ V _ _ _ S hS hk hdeg
  have hrn := S.r_lt_n
  let Stop : Stratum 𝒪[F] F V := ⟨S.chain, S.n, S.n - 1, S.b, by omega, S.valuation_ge⟩
  obtain ⟨T, hT, hTr, hcos, hslope, -⟩ := hRef F V Stop (hTop F V S hS)
  have hself : S.b ∈ Stop.coset := by
    show S.b - S.b ∈ S.chain.endFiltration (-(S.n - 1))
    rw [sub_self]
    exact zero_mem _
  have hβT : S.b ∈ T.coset := hcos hself
  refine ⟨T, hT, hβT, ?_⟩
  let : Nontrivial V := S.chain.nontrivialSpace
  have hle := elementDegree_le_finrank T.b hT.1.1.1
  rcases lt_or_eq_of_le hle with hlt | hfull
  · rw [hdeg]
    exact hlt
  exfalso
  -- `β` is congruent to a full-degree simple element at the top depth of `T`.
  have hdiff : S.b - T.b ∈ T.chain.endFiltration (-T.r) := hβT
  have hTrn := T.r_lt_n
  have hTb : T.b ∈ T.chain.endFiltration (-T.n) := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    have hv : ((-T.n : ℤ) : WithTop ℤ) ≤ T.chain.valuation T.b := by exact_mod_cast T.valuation_ge
    by_cases h0 : T.b = 0
    · rw [h0]
      exact zero_mem _
    obtain ⟨s, hs, hs'⟩ := exists_depth T.chain hπ h0
    rw [T.chain.valuation_eq_of_mem_of_notMem hs hs'] at hv
    exact T.chain.endFiltration_antitone (WithTop.coe_le_coe.mp hv) hs
  have hSbT : S.b ∈ T.chain.endFiltration (-T.n) := by
    have h := add_mem hTb (T.chain.endFiltration_antitone (show -T.n ≤ -T.r by omega) hdiff)
    simpa using h
  let T₁ : Stratum 𝒪[F] F V :=
    ⟨T.chain, T.n, T.r, S.b, T.r_lt_n, by exact_mod_cast le_valuation_of_mem T.chain hSbT⟩
  have hTT₁ : T.Equivalent T₁ := by
    apply Stratum.equivalent_of_sub_mem (S := T) (T := T₁) rfl rfl
    change T.b - S.b ∈ T.chain.endFiltration (-T.r)
    have h := neg_mem hdiff
    rwa [neg_sub] at h
  obtain ⟨hT₁, -⟩ := maximalSimpleReflection F V T T₁ hT hfull rfl rfl rfl hTT₁
  -- Both chains are normalized by `F[β]ˣ`, and `V` is a line over `F[β]`.
  obtain ⟨⟨hF, hA⟩, -⟩ := hS
  obtain ⟨⟨hF₁, hB⟩, -⟩ := hT₁.1
  let : Field (elementAlgebra S.b) := hF.toField
  obtain ⟨t, ht⟩ := lineChainTranslation (E := elementAlgebra S.b) S.chain T.chain hA hB
    (exists_line_generator S.b hF hdeg)
  -- The two chains have the same period, so the two levels agree.
  have hper := period_eq_of_translate ht
  have hn : T.n = S.n := by
    have hp : (0 : ℤ) < S.chain.period := by exact_mod_cast S.chain.period_pos
    change S.n * (T.chain.period : ℤ) = T.n * S.chain.period at hslope
    rw [← hper] at hslope
    exact (mul_right_cancel₀ hp.ne' hslope).symm
  -- Transport the simple stratum back to the original chain.
  have htr := chainTranslation 𝒪[F] F V Stop T₁ t ht hn (by simp [Stop, T₁, hTr, hn]) rfl
  have hsimple := htr.2.1.mpr hT₁
  have hlt := hsimple.2
  change criticalExponent S.chain S.b < _ at hlt
  rw [hk] at hlt
  have h1 := WithBot.coe_lt_coe.mp hlt
  have hStopr : Stop.r = S.n - 1 := rfl
  rw [hStopr] at h1
  omega

end Langlands.BushnellKutzko.PureApproximation
