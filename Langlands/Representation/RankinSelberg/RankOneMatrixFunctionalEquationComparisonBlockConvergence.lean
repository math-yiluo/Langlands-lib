import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonOriginalBlockZero
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonDualConvergence
import Langlands.Representation.RankinSelberg.UnequalRankFiniteExpansionProof
import Langlands.Representation.RankinSelberg.UnequalRankCompactSupportProof

/-! # Absolute convergence of the actual rank-one-pair block integrals

A finite pointwise Schwartz expansion, with model vectors in the original
coefficient image, turns every block integrand into a finite sum of products
of zero-row integrands and compactly supported rectangular tests.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uX

namespace RankOneBlockConvergence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance blockConvergenceTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance blockConvergenceValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance blockConvergenceLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance blockConvergenceT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance blockConvergenceSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance blockConvergenceScalarMeasurable : MeasurableSpace F.Carrier := borel _
local instance blockConvergenceScalarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance blockConvergenceGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance blockConvergenceGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance blockConvergenceGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance blockConvergenceGLSigmaCompact (n : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (n + 1)
local instance blockConvergenceUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F.Carrier) := borel _
local instance blockConvergenceUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
local instance blockConvergenceQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance blockConvergenceQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

/-- The actual rank-one quotient homeomorphism also transports a product
with any supplied s-finite rectangular measure. -/
theorem integrable_quotient_prod_iff {X : Type uX} [MeasurableSpace X]
    (ρ : Measure X) [SFinite ρ]
    (f : LeftUnipotentQuotient 0 F.Carrier × X → ℂ) :
    Integrable f ((rankOneQuotientHaar F.Carrier).prod ρ) ↔
      Integrable (fun gx : Langlands.GeneralLinear (0 + 1) F.Carrier × X =>
        f (Quotient.mk _ gx.1, gx.2)) ((generalLinearHaar F.Carrier 0).prod ρ) := by
  let e := (rankOneQuotientHomeomorph (F := F.Carrier)).symm.toMeasurableEquiv.prodCongr (MeasurableEquiv.refl X)
  have he : ((rankOneQuotientHaar F.Carrier).prod ρ) =
      Measure.map e ((generalLinearHaar F.Carrier 0).prod ρ) := by
    have hef : (e : (Langlands.GeneralLinear (0 + 1) F.Carrier × X) →
        LeftUnipotentQuotient 0 F.Carrier × X) =
        Prod.map (rankOneQuotientHomeomorph (F := F.Carrier)).symm (id : X → X) := by
      funext gx
      rfl
    rw [hef]
    have h := Measure.map_prod_map (generalLinearHaar F.Carrier 0) ρ
      (rankOneQuotientHomeomorph (F := F.Carrier)).symm.continuous.measurable (measurable_id : Measurable (id : X → X))
    simpa only [Measure.map_id, rankOneQuotientHaar] using h
  rw [he]
  exact integrable_map_equiv e f

section FixedShape

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  {j k : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (0 + (j + k + 1) + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ (0 + (j + k + 1)) σ)

/-- A finite pointwise Schwartz expansion and convergence of every diagonal
model restriction imply absolute product convergence of the actual block. -/
theorem converges_of_finite_expansion (s : ℂ)
    (f : (coefficientModel σ ℓ).toSubmodule)
    (hbase : ∀ v : (coefficientModel σ ℓ).toSubmodule,
      Integrable (fun g => v.val.val (appendIdentity 0 (j + k + 1) g) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
          (s - ((j + k + 1 : ℕ) : ℂ) / 2)) (generalLinearHaar F.Carrier 0))
    {d : ℕ} (φ : Fin d → SchwartzBruhat (Matrix (Fin j) (Fin (0 + 1)) F.Carrier))
    (fs : Fin d → (coefficientModel σ ℓ).toSubmodule)
    (hexp : ∀ g X, f.val.val (unequalRankMatrix j k g X) =
      ∑ i : Fin d, φ i X * (fs i).val.val (appendIdentity 0 (j + k + 1) g)) :
    UnequalRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData) j k
      (rankOneQuotientHaar F.Carrier) (rectangularMeasure ν j (0 + 1))
      f.val (rankOneTrivialModelOne ψ).val s := by
  rw [UnequalRankConverges, integrable_quotient_prod_iff F]
  have hi : ∀ i : Fin d, Integrable
      (fun gx : Langlands.GeneralLinear (0 + 1) F.Carrier ×
          Matrix (Fin j) (Fin (0 + 1)) F.Carrier =>
        ((fs i).val.val (appendIdentity 0 (j + k + 1) gx.1) *
          determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) gx.1
            (s - ((j + k + 1 : ℕ) : ℂ) / 2)) * φ i gx.2)
      ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν j (0 + 1))) := by
    intro i
    exact (hbase (fs i)).mul_prod
      ((φ i).continuous.integrable_of_hasCompactSupport (φ i).hasCompactSupport)
  have hsum := integrable_finsetSum (s := Finset.univ) (fun i _ => hi i)
  refine hsum.congr (Filter.Eventually.of_forall fun gx => ?_)
  dsimp only
  rw [unequalRankIntegrand_mk, rankOneTrivialModelOne_apply, mul_one, hexp, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Full Whittaker type gives the exact finite expansion used above. -/
theorem converges_of_diagonal_integrable
    (hσ : IsOfWhittakerType (0 + (j + k + 1))
      (standardCharacter ψ (0 + (j + k + 1))) σ) (hℓ : ℓ.val ≠ 0)
    (s : ℂ) (f : (coefficientModel σ ℓ).toSubmodule)
    (hbase : ∀ v : (coefficientModel σ ℓ).toSubmodule,
      Integrable (fun g => v.val.val (appendIdentity 0 (j + k + 1) g) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
          (s - ((j + k + 1 : ℕ) : ℂ) / 2)) (generalLinearHaar F.Carrier 0)) :
    UnequalRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData) j k
      (rankOneQuotientHaar F.Carrier) (rectangularMeasure ν j (0 + 1))
      f.val (rankOneTrivialModelOne ψ).val s := by
  have hs := unequalRankCompactSupport F F.canonicalTopologicalData 0 j k ψ V σ hσ ℓ hℓ f
  obtain ⟨d, φ, fs, hexp⟩ := unequalRankFiniteExpansion F F.canonicalTopologicalData
    0 j k ψ V σ hσ ℓ hℓ f hs
  exact converges_of_finite_expansion F ψ ν σ ℓ s f hbase φ fs hexp

end FixedShape

section AnyBlock

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ)

/-- Absolute convergence of every allowed block with the canonical second
vector and a specified quotient measure, each on a right half-plane. -/
def AllBlocksConvergeOnRight (μ : Measure (LeftUnipotentQuotient 0 F.Carrier)) : Prop :=
  ∀ (j k : ℕ) (hr : r = 0 + (j + k + 1)),
    ∃ b : ℝ, ∀ f : (coefficientModel σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re →
        UnequalRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData) j k
          μ (rectangularMeasure ν j (0 + 1))
          (InducedTailIntermediate.whittakerRankCast ψ hr f.val)
          (rankOneTrivialModelOne ψ).val s

/-- The supplied matrix convergence gives absolute convergence on a right
half-plane for every actual block and canonical-vector pair. -/
theorem convergesOnRight_of_matrix
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (hℓ : ℓ.val ≠ 0)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ))
    (j k : ℕ) (hr : r = 0 + (j + k + 1)) :
    ∃ b : ℝ, ∀ f : (coefficientModel σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re →
      UnequalRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData) j k
        (rankOneQuotientHaar F.Carrier) (rectangularMeasure ν j (0 + 1))
        (InducedTailIntermediate.whittakerRankCast ψ hr f.val)
        (rankOneTrivialModelOne ψ).val s := by
  subst r
  have hbase : ∃ b : ℝ, ∀ v : (coefficientModel σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re → Integrable
        (fun g => v.val.val (appendIdentity 0 (j + k + 1) g) *
          determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
            (s - ((j + k + 1 : ℕ) : ℂ) / 2)) (generalLinearHaar F.Carrier 0) := by
    obtain ⟨b, hb⟩ := RankOneBox.rankOneModel_convergesOnRight_of_matrix
      F ψ σ ℓ hσ.1.1 hMatrix
    refine ⟨b, fun v s hs => ?_⟩
    have h := hb v s hs
    convert h using 1
    funext g
    have hg : appendIdentity 0 (j + k + 1) g = rankOneEmbedding (0 + (j + k)) g := by
      apply Units.ext
      rw [rankOneEmbedding_val]
      ext a b
      cases a using Fin.cases <;> cases b using Fin.cases <;>
        simp [appendIdentity_entry, Matrix.diagonal_apply, eq_comm]
    rw [hg]
    simp only [rankOneModelIntegrand, glModelFunction]
    congr 2
    have hn : Nat.add 0 (j + k) = j + k := Nat.zero_add _
    rw [hn]
  obtain ⟨b, hb⟩ := hbase
  exact ⟨b, fun f s hs => converges_of_diagonal_integrable F ψ ν σ ℓ hσ hℓ s f
    (fun v => hb v s hs)⟩

/-- The actual matrix convergence supplies absolute convergence of all blocks
for every compatible rank-one quotient measure. -/
theorem allBlocksConvergeOnRight_of_matrix
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (hℓ : ℓ.val ≠ 0)
    (μ : Measure (LeftUnipotentQuotient 0 F.Carrier))
    (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier) (generalLinearHaar F.Carrier 0)
      (unipotentHaar F.Carrier 0) μ)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ)) :
    AllBlocksConvergeOnRight F ψ ν σ ℓ μ := by
  rw [eq_rankOneQuotientHaar_of_isCompatible F.Carrier μ hμ]
  exact convergesOnRight_of_matrix F ψ ν σ ℓ hσ hℓ hMatrix

/-- The actual complementary-block dual integrand is absolutely integrable
on a right half-plane, using the supplied inverse-transpose matrix assertions. -/
theorem dualBlockZero_convergesOnRight_of_iota (hrpos : 0 < r)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (hℓ : ℓ.val ≠ 0)
    (μ : Measure (LeftUnipotentQuotient 0 F.Carrier))
    (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier) (generalLinearHaar F.Carrier 0)
      (unipotentHaar F.Carrier 0) μ)
    (P : Polynomial ℂ)
    (hIota : GodementJacquet.Padic.IotaMatrixAnalyticAssertions F
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ) P)
    : ∃ b : ℝ, ∀ f : (coefficientModel σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re →
      UnequalRankConverges (ψ.scale (-1)) (normalizedAbsoluteValue F.canonicalTopologicalData)
        (r - 0 - 1) 0 μ (rectangularMeasure ν (r - 0 - 1) (0 + 1))
        (InducedTailIntermediate.whittakerRankCast (ψ.scale (-1)) (by omega)
          (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f.val)
            (blockWeylAt 0 r hrpos)))
        (secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val) s := by
  have hMd := (iotaMatrixAnalyticAssertions_firstDual_iff ψ σ ℓ
    F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier r) P).mp hIota
  have hconv := allBlocksConvergeOnRight_of_matrix F (ψ.scale (-1)) ν
    (inverseTransposePullback σ) (firstDualFunctional ψ σ ℓ)
    (isOfWhittakerType_firstDual ψ σ hσ) (firstDualFunctional_ne_zero ψ σ hℓ)
    μ hμ hMd.1 (r - 0 - 1) 0 (by omega)
  have h1 : secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val =
      (rankOneTrivialModelOne (ψ.scale (-1))).val := by
    apply Subtype.ext
    funext g
    simp only [secondDualFunction_apply, rankOneTrivialModelOne_apply]
  obtain ⟨b, hb⟩ := hconv
  refine ⟨b, fun f s hs => ?_⟩
  rw [h1]
  exact hb (translatedFirstDualModelEquiv ψ σ ℓ (blockWeylAt 0 r hrpos) f) s hs

end AnyBlock

end RankOneBlockConvergence

end Langlands.RankinSelberg
