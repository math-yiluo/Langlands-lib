import Langlands.Representation.RankinSelberg.LanglandsPairEpsilonFactorExistenceStatement
import Langlands.Representation.RankinSelberg.PadicSymmetricEpsilonFactor
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.Classification.GenericSegmentProductExhaustionProof
import Langlands.Representation.Classification.SegmentProductOrderedAssembly

/-!
# Epsilon factors of all pairs of square-integrable blocks

Every irreducible essentially square-integrable block is generic, so the
published generic epsilon construction supplies the factor of every pair of
blocks of two square-integrable Langlands data.
-/

noncomputable section

namespace Langlands.RankinSelberg

open CategoryTheory HarmonicAnalysis GeneralLinear PadicField.TopologicalData Derivative
open Classification

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Transporting an object to an equal rank and back preserves the object. -/
private def rankCastCancelIso {a b : ℕ} (h : a = b)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    (generalLinearRankCast T h).obj (h.symm ▸ π) ≅ π := by
  subst b
  exact Iso.refl _

/-- Every irreducible essentially square-integrable smooth positive-rank GL
representation is generic for every nontrivial unitary additive character. -/
theorem essentiallySquareIntegrable_isGeneric (n : ℕ)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier))
    (hπi : letI := T.topology; Representation.IsIrreducible π.representation)
    (hπ : letI := T.topology; T.IsEssentiallySquareIntegrable π.representation)
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier) :
    letI := T.topology; Whittaker.IsGeneric ψ n π.representation := by
  let := T.topology
  obtain ⟨Δ, hΔ, hhead⟩ :=
    (segmentEssentialSquareIntegrableClassification.{uF,uV} F T
      (n + 1) (Nat.succ_pos n) π hπi).mp hπ
  let d : SegmentProductDatum.{max uF uV,uF} T (n + 1) :=
    { length := 1
      segments := fun _ => Δ
      degree_sum := by simpa only [Fin.sum_univ_one] using hΔ
      blocks := fun _ => hΔ.symm ▸ π }
  have hd : d.HasSegmentHeads := fun _ => hhead
  have hu : d.multisegment.IsUnlinked := by
    intro Γ hΓ Λ hΛ
    have hΓ' : Γ = Δ := by
      simpa [SegmentProductDatum.multisegment, d] using hΓ
    have hΛ' : Λ = Δ := by
      simpa [SegmentProductDatum.multisegment, d] using hΛ
    subst Γ
    subst Λ
    exact Segment.not_isLinked_self Δ
  have e : d.induced ≅ π :=
    SegmentProductOrderedAssembly.singletonIso d rfl (0 : Fin 1) ≪≫
      rankCastCancelIso F T hΔ π
  exact (genericSegmentProductExhaustion.{uF,uV} T ψ n π).mpr
    ⟨d, hd, hu, ⟨e.symm⟩⟩

/-- Irreducible essentially square-integrable representations of positive
ranks, in either rank order, have an epsilon factor. -/
theorem essentiallySquareIntegrable_epsilonFactorExists
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) {m k : ℕ}
    (hm : 0 < m) (hk : 0 < k)
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear k F.Carrier))
    (hπi : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible π.representation)
    (hπ : letI := F.canonicalTopologicalData.topology
      F.canonicalTopologicalData.IsEssentiallySquareIntegrable π.representation)
    (hσi : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible σ.representation)
    (hσ : letI := F.canonicalTopologicalData.topology
      F.canonicalTopologicalData.IsEssentiallySquareIntegrable σ.representation) :
    ∃ e : ℂˣ × ℤ, letI := F.canonicalTopologicalData.topology
      IsPadicRankEpsilonFactor F ψ ν.val π.representation σ.representation e := by
  let := F.canonicalTopologicalData.topology
  cases m with
  | zero => exact absurd hm (lt_irrefl 0)
  | succ r =>
    cases k with
    | zero => exact absurd hk (lt_irrefl 0)
    | succ t =>
      exact ⟨_, genericSymmetricEpsilonData_isPadic F ψ ν.val ν.property
        π.representation σ.representation
        (essentiallySquareIntegrable_isGeneric.{uF,uV} F F.canonicalTopologicalData
          r π hπi hπ ψ)
        (essentiallySquareIntegrable_isGeneric.{uF,uW} F F.canonicalTopologicalData
          t σ hσi hσ ψ)⟩

/-- Every pair of blocks of square-integrable Langlands data, in the saturated
carrier universes, has its epsilon factor. -/
theorem squareIntegrableDataEpsilonExistence
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) {n t : ℕ}
    (d : SquareIntegrableLanglandsDatum.{max uF uV, uF} F.canonicalTopologicalData n)
    (d' : SquareIntegrableLanglandsDatum.{max uF uW, uF} F.canonicalTopologicalData t) :
    SquareIntegrableDataEpsilonExistence F ψ ν.val d d' := fun i j =>
  essentiallySquareIntegrable_epsilonFactorExists.{uF,uV,uW} F ψ ν
    (d.shape.positive i) (d'.shape.positive j) (d.blocks i) (d'.blocks j)
    (d.irreducible i) (d.essentiallySquareIntegrable i)
    (d'.irreducible j) (d'.essentiallySquareIntegrable j)

/-- The actual epsilon factor of two square-integrable data: the product of the
epsilon factors of all pairs of blocks, with its certificate. No existence
input is assumed; the block factors come from
`squareIntegrableDataEpsilonExistence`. -/
def squareIntegrableDataEpsilonFactorOfBlocks
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) {n t : ℕ}
    (d : SquareIntegrableLanglandsDatum.{max uF uV, uF} F.canonicalTopologicalData n)
    (d' : SquareIntegrableLanglandsDatum.{max uF uW, uF} F.canonicalTopologicalData t) :
    {e : ℂˣ × ℤ // IsSquareIntegrableDataEpsilonFactor F ψ ν.val d d' e} :=
  squareIntegrableDataEpsilonFactor F ψ ν.val d d'
    (squareIntegrableDataEpsilonExistence.{uF,uV,uW} F ψ ν d d')

/-- The epsilon existence statement follows from square-integrable exhaustion
and classification at both carrier universes alone: the block input of
`langlandsPairEpsilonFactorExistence_of_classification` is proved above.
Exhaustion and classification remain hypotheses here. -/
theorem langlandsPairEpsilonFactorExistence_of_exhaustion_classification
    (hex : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      SquareIntegrableLanglandsExhaustion.{uF, uV} F F.canonicalTopologicalData ∧
        SquareIntegrableLanglandsExhaustion.{uF, uW} F F.canonicalTopologicalData)
    (hcl : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      SquareIntegrableLanglandsClassification.{uF, uV} F F.canonicalTopologicalData ∧
        SquareIntegrableLanglandsClassification.{uF, uW} F F.canonicalTopologicalData) :
    LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW} :=
  langlandsPairEpsilonFactorExistence_of_classification hex hcl
    fun _ _ F ψ ν _ _ d d' => squareIntegrableDataEpsilonExistence.{uF,uV,uW} F ψ ν d d'

end Langlands.RankinSelberg
