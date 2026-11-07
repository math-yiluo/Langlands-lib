import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Automorphic.CuspidalWhittaker.AdelicCharacter
import Langlands.Global.Factors.HeckeAdditiveComponents
import Langlands.Correspondence.RankOneArithmeticEpsilonData

/-! # Actual additive inputs for associated-pair comparisons -/

noncomputable section

universe u

namespace Langlands.Global.HeckeFunctionalEquation

open Langlands.Automorphic

variable (K : Type u) [Field K] [NumberField K]

/-- The published standard adelic character, bundled with continuity and nontriviality. -/
def standardGlobalAdditiveCharacter : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K) where
  toAddChar := CuspidalWhittaker.adelicCharacter K
  continuous_toFun := CuspidalWhittaker.continuous_adelicCharacter K
  nontrivial := by
    intro h
    obtain ⟨x, hx⟩ := CuspidalWhittaker.exists_adelicCharacter_ne_one K
    exact hx (by rw [h, AddChar.one_apply])

@[simp]
theorem standardGlobalAdditiveCharacter_apply (x : Adeles K) :
    standardGlobalAdditiveCharacter K x = CuspidalWhittaker.adelicCharacter K x := rfl

theorem standardGlobalAdditiveCharacter_diagonal (x : K) :
    standardGlobalAdditiveCharacter K (diagonal K x) = 1 :=
  CuspidalWhittaker.adelicCharacter_algebraMap K x

/-- The Hecke and Whittaker interfaces insert the same additive local coordinate. -/
theorem finiteAdditiveInclusion_eq_finiteToAdeles_finiteSingle
    (v : FinitePlace K) (x : FiniteCompletion K v) :
    finiteAdditiveInclusion K v x =
      CuspidalWhittaker.finiteToAdeles K (CuspidalWhittaker.finiteSingle K v x) := by
  classical
  rfl

theorem finiteAdditiveRestriction_standardGlobalAdditiveCharacter (v : FinitePlace K) :
    finiteAdditiveRestriction (standardGlobalAdditiveCharacter K) v =
      CuspidalWhittaker.localCharacter K v := by
  apply AddChar.ext
  intro x
  change CuspidalWhittaker.adelicCharacter K (finiteAdditiveInclusion K v x) = _
  rw [finiteAdditiveInclusion_eq_finiteToAdeles_finiteSingle]
  rfl

theorem finiteAdditiveRestriction_standardGlobalAdditiveCharacter_ne_one (v : FinitePlace K) :
    finiteAdditiveRestriction (standardGlobalAdditiveCharacter K) v ≠ 1 := by
  rw [finiteAdditiveRestriction_standardGlobalAdditiveCharacter]
  intro h
  obtain ⟨x, hx⟩ := CuspidalWhittaker.exists_localCharacter_ne_one K v
  exact hx (by rw [h, AddChar.one_apply])

/-- The actual finite component of the standard character, in the canonical topology. -/
def standardFiniteAdditiveComponent (v : FinitePlace K) :
    Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v) := by
  letI : TopologicalSpace (FiniteCompletion K v) :=
    (CompletionPadic.padicField v).canonicalTopologicalData.topology
  exact
    { toAddChar := finiteAdditiveRestriction (standardGlobalAdditiveCharacter K) v
      continuous_toFun := by
        change @Continuous (FiniteCompletion K v) Circle
          (CompletionPadic.padicField v).canonicalTopologicalData.topology _
          (finiteAdditiveRestriction (standardGlobalAdditiveCharacter K) v)
        rw [← CompletionPadic.completion_topology_eq v]
        exact continuous_finiteAdditiveRestriction (standardGlobalAdditiveCharacter K) v
      nontrivial := finiteAdditiveRestriction_standardGlobalAdditiveCharacter_ne_one K v }

theorem isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent (v : FinitePlace K) :
    ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent
      (standardGlobalAdditiveCharacter K) v (standardFiniteAdditiveComponent K v) := by
  intro x
  rfl

theorem standardFiniteAdditiveComponent_apply (v : FinitePlace K) (x : FiniteCompletion K v) :
    standardFiniteAdditiveComponent K v x = CuspidalWhittaker.localCharacter K v x :=
  congrArg (fun χ : AddChar (FiniteCompletion K v) Circle => χ x)
    (finiteAdditiveRestriction_standardGlobalAdditiveCharacter K v)

theorem standardFiniteAdditiveComponent_eq_one_of_mem (v : FinitePlace K)
    (x : FiniteCompletion K v) (hx : x ∈ v.adicCompletionIntegers K) :
    standardFiniteAdditiveComponent K v x = 1 := by
  rw [standardFiniteAdditiveComponent_apply]
  exact CuspidalWhittaker.localCharacter_eq_one K hx

theorem existsUnique_selfDualMeasure_standardFiniteAdditiveComponent (v : FinitePlace K) :
    ∃! ν : Correspondence.LocalAdditiveHaarMeasure (CompletionPadic.padicField v),
      Correspondence.IsSelfDualMeasure (CompletionPadic.padicField v)
        (standardFiniteAdditiveComponent K v) ν :=
  Correspondence.existsUnique_localSelfDualMeasure _ (standardFiniteAdditiveComponent K v)

/-- Every number field admits the actual global and finite additive inputs used by
associated-pair comparison, with self-dual Haar measures at all finite places. -/
theorem exists_associatedAdditiveInputs :
    ∃ ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K),
      (∀ x : K, ψ (diagonal K x) = 1) ∧
      ∃ ψf : ∀ v : FinitePlace K,
          Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v),
        (∀ v, ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v (ψf v)) ∧
        ∃ ν : ∀ v, Correspondence.LocalAdditiveHaarMeasure (CompletionPadic.padicField v),
          ∀ v, Correspondence.IsSelfDualMeasure (CompletionPadic.padicField v) (ψf v) (ν v) := by
  refine ⟨standardGlobalAdditiveCharacter K, standardGlobalAdditiveCharacter_diagonal K,
    standardFiniteAdditiveComponent K,
    isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent K, ?_⟩
  exact ⟨fun v => Correspondence.localSelfDualHaar _ (standardFiniteAdditiveComponent K v),
    fun v => Correspondence.isSelfDual_localSelfDualHaar _ (standardFiniteAdditiveComponent K v)⟩

end Langlands.Global.HeckeFunctionalEquation
