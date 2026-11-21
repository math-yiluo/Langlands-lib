import Langlands.Global.Factors.CuspidalSupportInducedReduction
import Langlands.Global.Factors.CuspidalSupportCompactCoefficient
import Langlands.Global.Factors.CuspidalSupportCompactJacquet
import Langlands.Global.Factors.CuspidalSupportPlaceTensorAdmissibility
import Langlands.Global.Factors.CuspidalArchimedeanParameterPartial

/-! # From one projected cuspidal block realization to every place constituent -/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

namespace Langlands.Global

open Langlands.Automorphic Langlands.Archimedean Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

section Evaluations

variable {r k : ℕ} {m : Fin k → ℕ}
  (hm : ∑ i, (m i + 1) = r + 1) (T : ∀ i, CuspidalOperatorRealization F (m i))
  (Q : IrreducibleOperatorSubquotient F r)
  {W : Type u} [AddCommGroup W] [Module ℂ W] (q : W →ₗ[ℂ] Q.Space)

local notation "N" => r + 1
local notation "RK" => Matrix.unitaryGroup (Fin N) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin N) ℂ
local notation "RM" => Matrix (Fin N) (Fin N) ℝ
local notation "CM" => Matrix (Fin N) (Fin N) ℂ
private abbrev projectedBlockShape : BlockShape N :=
  ⟨k, fun i => m i + 1, fun i => Nat.succ_pos (m i), hm⟩

private abbrev blockCoefficientSpace := PiTensorProduct ℂ (fun i => ↥((T i).Space))
local notation "E" => blockCoefficientSpace T

/-- A real place source for the same projected block coefficient evaluation.
The quotient map intertwines the place actions, and the evaluations have
normalized block covariance and separate after compact translation. -/
def HasRealCuspidalBlockEvaluations (v : RP) : Prop :=
  ∃ (κ : Representation ℂ RK W) (π : (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (I : Type u) (ev : I → W →ₗ[ℂ] E),
    IsRealGKModule N κ π ∧
    IsPlaceQuotientIntertwining κ π
      (Q.subquotient.realPlaceCompactRepresentation v) (Q.subquotient.realPlaceLieAction v) q ∧
    (∀ y, IsBlockCompactEvaluation (B := projectedBlockShape hm) κ
      (fun i => (T i).realization.realPlaceCompactRepresentation v) (ev y)) ∧
    (∀ y, IsNormalizedBlockLieEvaluation (projectedBlockShape hm) π (realCuspidalBlockLie T v) (ev y)) ∧
    ∀ w, (∀ y k, ev y (κ k w) = 0) → w = 0

/-- A complex place source for the same projected block coefficient evaluation.
The Lie identity uses complex matrices viewed as real directions. -/
def HasComplexCuspidalBlockEvaluations (v : CP) : Prop :=
  ∃ (κ : Representation ℂ CK W) (π : (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (I : Type u) (ev : I → W →ₗ[ℂ] E),
    IsComplexGKModule N κ π ∧
    IsPlaceQuotientIntertwining κ π
      (Q.subquotient.complexPlaceCompactRepresentation v) (Q.subquotient.complexPlaceLieAction v) q ∧
    (∀ y, IsBlockCompactEvaluation (B := projectedBlockShape hm) κ
      (fun i => (T i).realization.complexPlaceCompactRepresentation v) (ev y)) ∧
    (∀ y, IsNormalizedBlockLieEvaluation (projectedBlockShape hm) π
      (complexCuspidalBlockLie T v) (ev y)) ∧
    ∀ w, (∀ y k, ev y (κ k w) = 0) → w = 0

private theorem realPlaceConstituent_of_cuspidalBlockEvaluations
    (hq : Function.Surjective q) (v : RP) (ds : Fin k → List RealBlock)
    (hp : ∀ i, (T i).realization.HasRealPlaceParameter v (ds i))
    (heval : HasRealCuspidalBlockEvaluations hm T Q q v) :
    Q.subquotient.HasRealPlaceStandardConstituent v (List.ofFn ds).flatten := by
  obtain ⟨κ, π, I, ev, hgk, hqOps, hEvK, hEvL, hsep⟩ := heval
  obtain ⟨e, he, heK, heL⟩ := exists_realStandardTensor_of_cuspidalBlockEvaluations T v ds hm hp
    hgk ev hEvK hEvL hsep
  let D := RealLeviSlices.flat ds
  obtain ⟨S, qS, hqS, hsS⟩ := exists_surjective_placeTensor_of_embedding κ π
    (realStandardRep N D) (realStandardLie N D)
    (Q.subquotient.realPlaceCompactRepresentation v) (Q.subquotient.realPlaceLieAction v)
    q hq hqOps e he heK heL
  have hrank : realRank D = N :=
    (RealLeviSlices.realRank_flat ds).trans
      ((Finset.sum_congr rfl fun i _ => (hp i).1).trans hm)
  have hnonzero : LinearMap.range qS ≠ ⊥ := by
    rw [LinearMap.range_eq_top.mpr hsS]
    exact top_ne_bot
  exact (archimedeanPlaceStandardConstituent_of_nonzero_tensor (M := _) Q.subquotient
    Q.irreducible Q.space_nontrivial).1 v D hrank qS hqS hnonzero

private theorem complexPlaceConstituent_of_cuspidalBlockEvaluations
    (hq : Function.Surjective q) (v : CP) (ds : Fin k → List ComplexCharacterData)
    (hp : ∀ i, (T i).realization.HasComplexPlaceParameter v (ds i))
    (heval : HasComplexCuspidalBlockEvaluations hm T Q q v) :
    Q.subquotient.HasComplexPlaceStandardConstituent v (List.ofFn ds).flatten := by
  obtain ⟨κ, π, I, ev, hgk, hqOps, hEvK, hEvL, hsep⟩ := heval
  obtain ⟨e, he, heK, heL⟩ := exists_complexStandardTensor_of_cuspidalBlockEvaluations T v ds hm hp
    hgk ev hEvK hEvL hsep
  let D := (List.ofFn ds).flatten
  obtain ⟨S, qS, hqS, hsS⟩ := exists_surjective_placeTensor_of_embedding κ π
    (complexStandardRep N D) (complexStandardLie N D)
    (Q.subquotient.complexPlaceCompactRepresentation v) (Q.subquotient.complexPlaceLieAction v)
    q hq hqOps e he heK heL
  have hrank : D.length = N := by
    change (List.ofFn ds).flatten.length = N
    rw [List.length_flatten, List.map_ofFn, List.sum_ofFn, ← hm]
    exact Finset.sum_congr rfl (fun i _ => (hp i).1)
  have hnonzero : LinearMap.range qS ≠ ⊥ := by
    rw [LinearMap.range_eq_top.mpr hsS]
    exact top_ne_bot
  exact (archimedeanPlaceStandardConstituent_of_nonzero_tensor (M := _) Q.subquotient
    Q.irreducible Q.space_nontrivial).2 v D hrank qS hqS hnonzero

end Evaluations

/-- The common cuspidal block data give a finite induced subquotient and one
surjective quotient map for the archimedean block evaluation comparisons. -/
def HasProjectedCuspidalBlockRealization {r : ℕ} (Q : IrreducibleOperatorSubquotient F r) : Prop :=
  ∃ (k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i)),
    FiniteParametrizedBlockInduction.HasSubquotient
      (⟨k, fun i => m i + 1, fun i => Nat.succ_pos (m i), hm⟩ : BlockShape (r + 1))
      (fun i => (T i).realization.finiteRepresentation) Q.subquotient.finiteRepresentation ∧
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module ℂ W) (q : W →ₗ[ℂ] Q.Space),
      Function.Surjective q ∧
      (∀ v : RP, HasRealCuspidalBlockEvaluations hm T Q q v) ∧
      ∀ v : CP, HasComplexCuspidalBlockEvaluations hm T Q q v

/-- Common projected cuspidal block realizations and the real-place cuspidal
parameters imply the exact every-place cuspidal support proposition. -/
theorem cuspidalSupportEveryPlace_of_projectedCuspidalBlocks
    (hModel : ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
      (r : ℕ) (Q : IrreducibleOperatorSubquotient F r), HasProjectedCuspidalBlockRealization Q)
    (hParam : ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
      (r : ℕ) (T : CuspidalOperatorRealization F r) (v : {v : NumberField.InfinitePlace F // v.IsReal}),
      ∃ ds, T.realization.HasRealPlaceParameter v ds) : CuspidalSupportEveryPlaceStatement.{u} := by
  classical
  intro F _ _ _ r Q
  obtain ⟨k, m, hm, T, hf, W, _, _, q, hq, hR, hC⟩ := hModel F r Q
  obtain ⟨P, hP, hfP⟩ := exists_finiteInducedConstituent_of_parametrizedInduction hm Q hf
  refine ⟨k, m, hm, T, P, hP, hfP, ?_, ?_⟩
  · intro v
    have hp (i : Fin k) := hParam F (m i) (T i) v
    choose ds hds using hp
    exact ⟨ds, hds, realPlaceConstituent_of_cuspidalBlockEvaluations hm T Q q hq v ds hds (hR v)⟩
  · intro v
    have hp (i : Fin k) := exists_cuspidalComplexPlaceParameter (T i) v
    choose ds hds using hp
    exact ⟨ds, hds, complexPlaceConstituent_of_cuspidalBlockEvaluations hm T Q q hq v ds hds (hC v)⟩

end Langlands.Global
