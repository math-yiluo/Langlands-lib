import Langlands.BushnellKutzko.PureStratumApproximationFinalStep

/-! # The pure-stratum approximation theorem from (2.3.11), (2.3.4) and (2.3.12)

Proof of BK93 (2.4.1)(i), printed pp. 66–71, in the witness form
`PureStratumSimpleApproximationStatement`, from the propositions `TopNonsplitPremise` ((2.3.11)),
`NonsplitRefinementPremise` ((2.3.4), used over `F` and over a generated field) and
`SplitObstructionPremise` ((2.3.12)). The two remaining steps of the source proof, (2.4.5) and its
final step, are proved in `PureStratumApproximationChainImprovement` and
`PureStratumApproximationFinalStep`.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uV

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- BK93 (2.4.1)(i) in the critical full-degree case: choose an optimal candidate, form the
derived stratum of its difference with `β`, and exclude every case except the one producing the
required witness. -/
theorem maximalCriticalApproximation_of_premises (hTop : TopNonsplitPremise.{uF, uV})
    (hRef : NonsplitRefinementPremise.{uF, uV}) (hRefE : NonsplitRefinementPremise.{uV, uV})
    (hSplit : SplitObstructionPremise.{uF, uV, uV}) :
    MaximalCriticalApproximationStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ S hS hk hdeg
  classical
  let : Nontrivial V := S.chain.nontrivialSpace
  obtain ⟨T₀, ⟨hT₀, hT₀β, hT₀deg⟩, hopt⟩ :=
    optimalCandidate F V S hS (candidateSeed hTop hRef F V S hS hk hdeg)
  have hself : S.b ∈ S.coset := by
    show S.b - S.b ∈ S.chain.endFiltration (-S.r)
    rw [sub_self]
    exact zero_mem _
  -- The derived stratum of `β − T₀.b` over `E = F[T₀.b]`.
  obtain ⟨hE, hEn⟩ := hT₀.1.1
  let : Field (elementAlgebra T₀.b) := hE.toField
  obtain ⟨s⟩ := (tameCorestriction F V (elementAlgebra T₀.b)).1
  have hdiff : S.b - T₀.b ∈ T₀.chain.endFiltration (-T₀.r) := hT₀β
  have hsb : (s (S.b - T₀.b)).restrictScalars F ∈ T₀.chain.endFiltration (-T₀.r) := by
    have h := (tameCorestriction F V (elementAlgebra T₀.b)).2.2 s T₀.chain hEn (-T₀.r)
    have hmem : s (S.b - T₀.b) ∈ s '' (T₀.chain.endFiltration (-T₀.r) : Set _) :=
      ⟨_, hdiff, rfl⟩
    rw [h] at hmem
    exact hmem
  have hrn₀ := T₀.r_lt_n
  let D : Stratum (subfieldIntegers F (elementAlgebra T₀.b)) (elementAlgebra T₀.b) V :=
    ⟨T₀.chain.subfieldChain (elementAlgebra T₀.b) hEn, T₀.r, T₀.r - 1, s (S.b - T₀.b),
      by omega, by
        rw [valuation_subfieldChain]
        exact_mod_cast le_valuation_of_mem T₀.chain hsb⟩
  have hD : T₀.IsDerivedStratum (elementAlgebra T₀.b) (S.b - T₀.b) s D :=
    ⟨hT₀, ⟨elementGenerator T₀.b, subfieldEmbedding_elementGenerator T₀.b hE,
      adjoin_elementGenerator T₀.b⟩, hdiff, fun i => Set.ext fun v => Iff.rfl, rfl, rfl, rfl⟩
  by_cases hns : ∃ x : elementAlgebra T₀.b, ∃ y ∈ D.coset,
      IsNilpotent (y - algebraMap (elementAlgebra T₀.b) (Module.End (elementAlgebra T₀.b) V) x)
  · -- (2.4.5) gives a candidate of the same degree and smaller normalized depth.
    exfalso
    obtain ⟨T, hT, hTβ, hTlt, he, hf⟩ :=
      chainImprovement F V (elementAlgebra T₀.b) S.b T₀ s D hD hns
    have hdegT : elementDegree F T.b = elementDegree F T₀.b := by
      rw [← elementRamificationIndex_mul_residueDegree T.b hT.1.1.1,
        ← elementRamificationIndex_mul_residueDegree T₀.b hE, he, hf]
    have hTc : elementDegree F T.b < elementDegree F S.b := hdegT ▸ hT₀deg
    have hle := (hopt T hT hTβ hTc).2 hdegT
    linarith
  simp only [not_exists, not_and] at hns
  have hfund : D.IsFundamental := ⟨rfl, fun y hy => by simpa using hns 0 y hy⟩
  have hnsplit : ¬ D.IsSplit := by
    intro hsp
    apply hSplit F V (elementAlgebra T₀.b) T₀ (S.b - T₀.b) s D hD hsp
    have hsum : T₀.b + (S.b - T₀.b) = S.b := by abel
    rw [hsum]
    exact hS.1.1
  rcases improvement_or_increase hRefE S.b T₀ s D hD hfund hnsplit with
    ⟨T, hT, hTβ, hTlt, he, hf⟩ | ⟨T, U, hUc, hUn, hUr, hT, hTβ, hU, hUβ, hUk, hdegU, heU, hfU⟩
  · -- A candidate of the same degree and smaller normalized depth contradicts the choice of `T₀`.
    exfalso
    have hdegT : elementDegree F T.b = elementDegree F T₀.b := by
      rw [← elementRamificationIndex_mul_residueDegree T.b hT.1.1.1,
        ← elementRamificationIndex_mul_residueDegree T₀.b hE, he, hf]
    have hTc : elementDegree F T.b < elementDegree F S.b := hdegT ▸ hT₀deg
    have hle := (hopt T hT hTβ hTc).2 hdegT
    linarith
  rcases lt_or_eq_of_le (elementDegree_le_finrank U.b hU.1.1.1) with hlt | hUfull
  · -- A candidate of larger degree contradicts the maximality of the degree of `T₀`.
    exfalso
    have hc : elementDegree F U.b < elementDegree F S.b := by rw [hdeg]; exact hlt
    have := (hopt U hU hUβ hc).1
    omega
  -- `F[U.b]` is maximal; `β` itself is simple of full degree on the chain of `U`.
  have hrnU := U.r_lt_n
  have hUb : U.b ∈ U.chain.endFiltration (-U.n) :=
    mem_endFiltration_of_le_valuation U.chain (by exact_mod_cast U.valuation_ge)
  have hdU : S.b - U.b ∈ U.chain.endFiltration (-U.r) := hUβ
  have hβU : S.b ∈ U.chain.endFiltration (-U.n) := by
    have h := add_mem hUb (U.chain.endFiltration_antitone (show -U.n ≤ -U.r by omega) hdU)
    simpa using h
  let U₁ : Stratum 𝒪[F] F V :=
    ⟨U.chain, U.n, U.r, S.b, U.r_lt_n, by exact_mod_cast le_valuation_of_mem U.chain hβU⟩
  have hUU₁ : U.Equivalent U₁ := by
    apply Stratum.equivalent_of_sub_mem (S := U) (T := U₁) rfl rfl
    change U.b - S.b ∈ U.chain.endFiltration (-U.r)
    have h := neg_mem hdU
    rwa [neg_sub] at h
  obtain ⟨hU₁, -⟩ := maximalSimpleReflection F V U U₁ hU hUfull rfl rfl rfl hUU₁
  have h5 := (stratumEquivalence F V U U₁ hUU₁).2.2.2 hU hU₁
  -- The chain of `U` is a translate of the original chain.
  obtain ⟨hF, hA⟩ := hS.1
  obtain ⟨hF₁, hB⟩ := hU₁.1.1
  let : Field (elementAlgebra S.b) := hF.toField
  obtain ⟨t, ht⟩ := lineChainTranslation (E := elementAlgebra S.b) S.chain U.chain hA hB
    (exists_line_generator S.b hF hdeg)
  have hkU : criticalExponent S.chain S.b = ((-T.r : ℤ) : WithBot ℤ) := by
    rw [criticalExponent_eq_of_translate ht S.b]
    have hc : criticalExponent U.chain S.b = criticalExponent U.chain U.b := h5.2.1.symm
    rw [hc, hUk]
  have hrT : T.r = S.r := by
    rw [hk] at hkU
    have := WithBot.coe_injective hkU
    omega
  have hβT' : ∀ i, S.chain.lattice i = T.chain.lattice (i + t) := by
    rw [← hUc]
    exact ht
  have hper : S.chain.period = T.chain.period := period_eq_of_translate hβT'
  have hslope := pureCosetSlope F V S T hS hT.1 S.b hself hTβ
  have hTn : T.n = S.n := by
    have hp : (0 : ℤ) < S.chain.period := by exact_mod_cast S.chain.period_pos
    rw [← hper] at hslope
    exact (mul_right_cancel₀ hp.ne' hslope).symm
  -- The witness: the element of `T` on the original chain.
  have hvalW : ((-S.n : ℤ) : WithTop ℤ) ≤ S.chain.valuation T.b := by
    rw [valuation_eq_of_translate hβT' T.b, hT.1.2, hTn]
    exact_mod_cast le_refl (-S.n)
  let W : Stratum 𝒪[F] F V := ⟨S.chain, S.n, S.r, T.b, S.r_lt_n, by exact_mod_cast hvalW⟩
  have htr := chainTranslation 𝒪[F] F V W T t hβT' hTn hrT rfl
  have hW : W.IsSimple := htr.2.1.mpr hT
  have hSW : S.Equivalent W := by
    apply Stratum.equivalent_of_sub_mem (S := S) (T := W) rfl rfl
    have h : S.b ∈ W.coset := by rw [htr.2.2.1]; exact hTβ
    exact h
  refine ⟨W, rfl, rfl, rfl, hW, hSW, ?_, ?_⟩
  · change elementRamificationIndex F T.b ∣ elementRamificationIndex F S.b
    have h := h5.2.2.1
    change elementRamificationIndex F U.b = elementRamificationIndex F S.b at h
    rw [← h]
    exact heU
  · change elementResidueDegree F T.b ∣ elementResidueDegree F S.b
    have h := h5.2.2.2
    change elementResidueDegree F U.b = elementResidueDegree F S.b at h
    rw [← h]
    exact hfU

/-- **BK93 (2.4.1)(i)** from (2.3.11), (2.3.4) over the base field and over the generated field
of the approximating element, and (2.3.12). -/
theorem pureStratumSimpleApproximation_of_premises (hTop : TopNonsplitPremise.{uF, uV})
    (hRef : NonsplitRefinementPremise.{uF, uV}) (hRefE : NonsplitRefinementPremise.{uV, uV})
    (hSplit : SplitObstructionPremise.{uF, uV, uV}) :
    PureStratumSimpleApproximationStatement.{uF, uV} :=
  pureStratumApproximationCriticalReduction
    (pureStratumApproximationMaximalReduction
      (maximalCriticalApproximation_of_premises hTop hRef hRefE hSplit))

end Langlands.BushnellKutzko.PureApproximation
