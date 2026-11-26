import Langlands.Global.RankinSelberg.RealAdjacentRankOneGeneration
import Langlands.Global.RankinSelberg.RealAdjacentDiscreteGeneration
import Langlands.Global.RankinSelberg.RealOrdinaryCharacterTransport
import Langlands.Global.RankinSelberg.RealOrdinaryGenerationPermutation
import Langlands.LocalFactor.RealBlockRankOne
import Langlands.LocalFactor.RealPairLFactorNormalization

/-! # Ordinary normalized generation for the real ranks two and one -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.RankinSelbergGlobal.RealAdjacentRankTwoAssembly

open ArchimedeanLocal Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open RealAdjacentRankOne RealAdjacentDiscreteGeneration RealCharacterChange
open RealJacquetFrobenius (charData)

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

private def finiteSumFor (D : RealQuotientMeasureData 0)
    (U : Submodule ℂ (Langlands.GeneralLinear 2 ℝ → ℂ)) (V : Submodule ℂ (Langlands.GeneralLinear 1 ℝ → ℂ))
    (L : ReciprocalEntire) : Prop :=
  HasFiniteOrdinaryNormalizationSum (fun i : U × V => realUnequalIntegral (Nat.lt_succ_self 0) D i.1.val i.2.val) L

private theorem finiteSum_of_modelFactor_eq (D : RealQuotientMeasureData 0) {ds es fs : List RealBlock}
    (hM : realWhittakerModel 1 fs 1 = realWhittakerModel 1 ds 1)
    (hL : realPairLFactor fs es = realPairLFactor ds es)
    (hS : HasFiniteOrdinaryNormalizationSum (realOrdinaryUnequalTest (Nat.lt_succ_self 0) fs es 1 D)
      (realPairLFactor fs es)) :
    HasFiniteOrdinaryNormalizationSum (realOrdinaryUnequalTest (Nat.lt_succ_self 0) ds es 1 D)
      (realPairLFactor ds es) := by
  change finiteSumFor D (realWhittakerModel 1 fs 1) (realWhittakerModel 0 es (-1)) (realPairLFactor fs es) at hS
  change finiteSumFor D (realWhittakerModel 1 ds 1) (realWhittakerModel 0 es (-1)) (realPairLFactor ds es)
  rwa [← hM, ← hL]

private theorem rankTwo_cases (ds : List RealBlock) (hd : realRank ds = 2) :
    (∃ c d : RealCharacterData, ds = [.character c, .character d]) ∨
      (∃ d : ComplexCharacterData, ds = [.induced d]) := by
  cases ds with
  | nil => simp [realRank] at hd
  | cons b ds =>
      cases b with
      | character c =>
          have h : realRank ds = 1 := by simp only [realRank_cons, RealBlock.rank] at hd; omega
          obtain ⟨d, rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one h
          exact Or.inl ⟨c, d, rfl⟩
      | induced d =>
          cases ds with
          | nil => exact Or.inr ⟨d, rfl⟩
          | cons b ds =>
              cases b <;> simp only [realRank_cons, RealBlock.rank] at hd <;> omega

private theorem adjacentRankTwo_at_one (ds es : List RealBlock) (hd : realRank ds = 2)
    (he : realRank es = 1)
    (hi : IsIrreducibleGKModule (realStandardRep 2 ds) (realStandardLie 2 ds))
    (D : RealQuotientMeasureData 0) :
    HasFiniteOrdinaryNormalizationSum
      (realOrdinaryUnequalTest (Nat.lt_succ_self 0) ds es 1 D) (realPairLFactor ds es) := by
  obtain ⟨e, rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one he
  rcases rankTwo_cases ds hd with ⟨c, d, rfl⟩ | ⟨d, rfl⟩
  · by_cases hcd : d.exponent.re ≤ c.exponent.re
    · exact realAdjacentRankOneClosedChamber c d e hcd D
    · have hp : ([.character c, .character d] : List RealBlock).Perm [.character d, .character c] := by
        apply List.Perm.swap
      have hm := (realWhittakerModels_of_perm_irreducible hp hd hi).2 1
      exact finiteSum_of_modelFactor_eq D hm (realPairLFactor_perm hp.symm (List.Perm.refl _))
        (realAdjacentRankOneClosedChamber d c e (le_of_not_ge hcd) D)
  · by_cases hw : d.weight = 0
    · let c₁ := charData 1 d.exponent
      let c₂ := charData 0 d.exponent
      let fs : List RealBlock := [.character c₁, .character c₂]
      have hEq : realStandardModule 2 [.induced d] = realStandardModule 2 fs := by
        simpa [realBlockExpand, hw, fs, c₁, c₂] using realStandardModule_append_expand 2 [] [] (.induced d)
      have hM : realWhittakerModel 1 fs 1 = realWhittakerModel 1 [.induced d] 1 :=
        le_antisymm (realWhittakerModel_le_of_surjective 1 (RealSurjectiveIntertwinerExists.of_eq hEq))
          (realWhittakerModel_le_of_surjective 1 (RealSurjectiveIntertwinerExists.of_eq hEq.symm))
      have hLists : ([.induced d] : List RealBlock).flatMap realBlockNormalize = fs := by
        simp [realBlockNormalize, realBlockExpand, hw, RealBlock.positiveWeight, fs, c₁, c₂]
      have hL := realPairLFactor_normalize_left [.induced d] [.character e]
      rw [hLists] at hL
      exact finiteSum_of_modelFactor_eq D hM hL (realAdjacentRankOneClosedChamber c₁ c₂ e le_rfl D)
    · exact realAdjacentDiscreteGeneration d hw e D

/-- The actual ordinary generation claims at real ranks two and one, for the
supplied irreducible upper standard module and arbitrary compatible quotient data. -/
def RealAdjacentRankTwoAssemblyStatement : Prop :=
  ∀ (ds es : List RealBlock), realRank ds = 2 → realRank es = 1 →
    IsIrreducibleGKModule (realStandardRep 2 ds) (realStandardLie 2 ds) →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData 0),
      HasCoveringOrdinaryNormalizations
        (realOrdinaryUnequalTest (Nat.lt_succ_self 0) ds es a D) (realPairLFactor ds es) ∧
      ((a = 1 ∨ a = -1) → HasFiniteOrdinaryNormalizationSum
        (realOrdinaryUnequalTest (Nat.lt_succ_self 0) ds es a D) (realPairLFactor ds es))

theorem realAdjacentRankTwoAssembly : RealAdjacentRankTwoAssemblyStatement := by
  intro ds es hd he hi a D
  let D' := leadingCharacterMeasure 1 a D
  have h := adjacentRankTwo_at_one ds es hd he hi D'
  let Cov (b : ℝˣ) := HasCoveringOrdinaryNormalizations
    (realOrdinaryUnequalTest (Nat.lt_succ_self 0) ds es b D) (realPairLFactor ds es)
  let Sum (b : ℝˣ) := HasFiniteOrdinaryNormalizationSum
    (realOrdinaryUnequalTest (Nat.lt_succ_self 0) ds es b D) (realPairLFactor ds es)
  refine ⟨?_, fun ha => ?_⟩
  · exact (congrArg Cov (one_mul a)).mp
      (realUnequalCoverage_scale (Nat.lt_succ_self 0) a (Or.inl rfl) D h.covering)
  · have habs : |(a : ℝ)| = 1 := by rcases ha with rfl | rfl <;> simp
    exact (congrArg Sum (one_mul a)).mp
      (realUnequalFiniteSum_scale (Nat.lt_succ_self 0) a habs D h)

end Langlands.Global.RankinSelbergGlobal.RealAdjacentRankTwoAssembly
