import Langlands.BaseChange.TwistedCharacter.UnramifiedTraceFamily
import Langlands.Representation.Classification.BernsteinUnitaryProductIrreducibilityProof
import Langlands.Representation.Classification.TemperedUnitarityProof
import Langlands.Representation.Unitary.Twist

/-! # Standard twisted traces as specializations of regular unramified families -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis MeasureTheory PadicField.TopologicalData

universe u v w

section Padic

variable {F : Type u} [Field F] [TopologicalSpace F] {p : ℕ} [Fact p.Prime]
  {E : PadicField.{v} p} [Algebra F E.Carrier] (T : E.TopologicalData)

/-- The unramified parameter of the real determinant power `|det|^s`. -/
def realPowerParameter (s : ℝ) : ℂˣ :=
  realPowerCharacter T.normalizedAbsUnits s T.uniformizerUnit

theorem determinantPowerCharacter_eq_determinantUnramified (m : ℕ) (s : ℝ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.determinantPowerCharacter m s = determinantUnramified E.Carrier m (realPowerParameter T s) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact T.realPowerDeterminant_eq_unramifiedCharacter m s

variable (hModule : letI := T.topology; IsModuleTopology F E.Carrier)
  (σ : E.Carrier ≃ₐ[F] E.Carrier)

/-- The blocks of a tempered datum are admissible. -/
theorem temperedDatum_blocks_isAdmissible {n : ℕ} (t : T.TemperedLanglandsDatum.{w} n)
    (i : Fin t.shape.length) :
    letI := T.topology
    IsAdmissible (t.blocks i).representation := by
  let := T.topology
  exact (t.tempered i).isAdmissible

include hModule in
/-- The half modulus of the supplied realization is invariant under `σ`. -/
theorem leviHalfModulus_leviAut_padic {n : ℕ} (B : BlockShape n) (m : B.Levi E.Carrier) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    T.leviHalfModulus B (leviAut σ B m) = T.leviHalfModulus B m := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  apply Units.ext
  have hm : T.leviModulus B (leviAut σ B m) = T.leviModulus B m := leviModulus_leviAut σ B m
  rw [leviHalfModulus_apply, leviHalfModulus_apply, hm]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The twisted trace of a σ-stable standard module is the value of the unramified family of
its tempered blocks at the parameters of its real exponents. -/
theorem standardTrace_eq_standardFamilyTrace {n : ℕ} (t : T.TemperedLanglandsDatum.{w} n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    ∀ [T2Space (GeneralLinear n E.Carrier)]
      [LocallyCompactSpace (GeneralLinear n E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
      [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
      (μ : Measure (GeneralLinear n E.Carrier)) [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant]
      (A : ∀ i, SigmaIntertwiner σ (t.shape.size i) (t.blocks i).representation),
      twistedDistribution μ t.standardModule.representation (temperedStandard_isAdmissible T t)
          (temperedStandardSigmaIntertwiner T hModule σ t A).toLinearMap =
        unramifiedFamilyTrace σ t.shape id (fun i => (t.blocks i).representation) A
          (T.leviHalfModulus t.shape) (T.isOpen_ker_leviHalfModulus t.shape)
          (leviHalfModulus_leviAut_padic T hModule σ t.shape) μ (temperedDatum_blocks_isAdmissible T t)
          (fun i => realPowerParameter T (t.exponent i)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _ _ A
  have h : twist (leviUnramified E.Carrier t.shape id (fun i => realPowerParameter T (t.exponent i)))
      (familyInducing t.shape (fun i => (t.blocks i).representation) (T.leviHalfModulus t.shape)) =
      twist (T.leviHalfModulus t.shape)
        (t.shape.blockTensor (fun i => (T.twistedBlocks t.shape t.blocks t.exponent i).representation)) := by
    rw [twist_familyInducing]
    congr 2
    funext i
    change twist _ _ = twist (T.determinantPowerCharacter (t.shape.size i) (t.exponent i)) _
    rw [determinantPowerCharacter_eq_determinantUnramified]
    rfl
  let B := t.shape
  let R (i : Fin B.length) := (T.twistedBlocks B t.blocks t.exponent i).representation
  let C (i : Fin B.length) : SigmaIntertwiner σ (B.size i) (R i) :=
    twistTwistedIntertwiner (entrywiseAut σ (B.size i))
      (T.determinantPowerCharacter (B.size i) (t.exponent i))
      (determinantPowerCharacter_entrywiseAut T hModule σ _ _) (A i)
  let Ξ := B.blockTensor R
  let κ := T.leviHalfModulus B
  let Ξ' := twist κ Ξ
  let A' := twistTwistedIntertwiner (leviAut σ B) κ (leviHalfModulus_leviAut_padic T hModule σ B)
    (leviTensorIntertwiner σ B C)
  have hI : IsAdmissible (Induction.smoothInduced (B.parabolic E.Carrier)
      (Ξ'.comp (B.leviProjection E.Carrier))) := temperedStandard_isAdmissible T t
  have key : twistedDistribution μ t.standardModule.representation (temperedStandard_isAdmissible T t)
      (temperedStandardSigmaIntertwiner T hModule σ t A).toLinearMap =
      twistedDistribution μ _ hI (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ' A').toLinearMap :=
    rfl
  have h2 := twistedDistribution_inducedSigma_congr σ B μ (Ξ₂ := Ξ') h
    (twistTwistedIntertwiner (leviAut σ B) _
      (leviUnramified_leviAut E.Carrier B id σ _)
      (familyInducingIntertwiner σ B _ A _ (leviHalfModulus_leviAut_padic T hModule σ B))) A' rfl
    (isAdmissible_familyInduced B id _ _ (T.isOpen_ker_leviHalfModulus B)
      (temperedDatum_blocks_isAdmissible T t) _) hI
  exact key.trans h2.symm

set_option maxHeartbeats 400000 in
/-- A unitary unramified twist of an irreducible unitarizable block family has irreducible
and unitarizable normalized product (Bernstein). -/
theorem normalizedProduct_unitaryTwist {n : ℕ} (B : BlockShape n)
    (δ : letI := T.topology; ∀ i, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (B.size i) E.Carrier))
    (hirr : letI := T.topology; ∀ i, (δ i).representation.IsIrreducible)
    (hunit : letI := T.topology; ∀ i, IsUnitarizable (δ i).representation)
    {r : ℕ} (g : Fin B.length → Fin r) (z : Fin r → ℂˣ) (hz : ∀ k, ‖(z k : ℂ)‖ = 1) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B (fun i =>
        twist (determinantUnramified E.Carrier (B.size i) (z (g i))) (δ i).representation)).IsIrreducible ∧
      IsUnitarizable (T.normalizedProductInduced B (fun i =>
        twist (determinantUnramified E.Carrier (B.size i) (z (g i))) (δ i).representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let δ' (i : Fin B.length) : SmoothRep.{0,v,max v w} ℂ (GeneralLinear (B.size i) E.Carrier) :=
    (δ i).twist (determinantUnramified E.Carrier (B.size i) (z (g i)))
      (isOpen_ker_determinantUnramified E.Carrier _ _)
  have h := Classification.bernsteinUnitaryProductIrreducibility.{v,w} E T n B δ' fun i =>
    ⟨(isIrreducible_twist_iff _ _).mpr (hirr i),
      (isUnitarizable_twist_iff _ (norm_determinantUnramified E.Carrier _ _ (hz _)) _).mpr (hunit i)⟩
  have e1 : ((T.normalizedProductInductionFunctor B).obj δ').representation =
      T.normalizedProductInduced B (fun i => (δ' i).representation) :=
    T.normalizedProductInductionFunctor_obj B δ'
  rw [e1] at h
  let e := T.normalizedProductInducedEquiv B (σ := fun i => (δ' i).representation)
    (τ := fun i => twist (determinantUnramified E.Carrier (B.size i) (z (g i))) (δ i).representation)
    (fun i => Representation.Equiv.refl _)
  exact ⟨(isIrreducible_iff_of_equiv e).mp h.1, (isUnitarizable_iff_of_equiv e).mp h.2⟩

/-- Irreducible tempered blocks are unitarizable. -/
theorem isUnitarizable_of_isTempered {m : ℕ} (hm : 0 < m)
    (δ : letI := T.topology; SmoothRep.{0,v,w} ℂ (GeneralLinear m E.Carrier))
    (hirr : letI := T.topology; δ.representation.IsIrreducible)
    (htemp : letI := T.topology; T.IsTempered δ.representation) :
    letI := T.topology
    IsUnitarizable δ.representation := by
  let := T.topology
  exact glTemperedUnitarity.{v,w} p E T m hm _ δ.representation hirr htemp

end Padic

end Langlands.BaseChange
