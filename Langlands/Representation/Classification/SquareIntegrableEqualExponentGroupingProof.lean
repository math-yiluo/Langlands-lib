import Langlands.Representation.Classification.ChosenUnitaryNormalizationProof
import Langlands.Representation.Classification.OrderedExponentGroupingProof
import Langlands.Representation.Classification.SquareIntegrableBlockInductionProof
import Langlands.Representation.Classification.TemperedBlockStatement
import Langlands.Representation.Classification.TwistedProductCharacterTwistProof
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Twist.AlgebraProof
import Langlands.Representation.Twist.SubquotientProof

/-!
# Equal-exponent grouping of square-integrable Langlands blocks

Normalize the original blocks at their chosen unitary exponents, induce each
ordered equal-exponent run, and compose the published twist and regrouping
isomorphisms to identify the original induced representation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Use the published character-twist theorem to undo a common normalizing
exponent after inducing the normalized factors. -/
private theorem groupedCommonExponentIso
    (n : ℕ) (hn : 0 < n) (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) (s : ℝ) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor B).obj σ ≅
      T.segmentFactor ((T.normalizedProductInductionFunctor B).obj
        (fun i => T.segmentFactor (σ i) (-s))) s) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let χ : Induction.SmoothCharacter ℂ F.Carrierˣ := {
    toMonoidHom := realPowerCharacter T.normalizedAbsUnits s
    isOpen_ker := isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits s }
  obtain ⟨E⟩ := twistedProductCharacterTwist.{uF,uV} F T n hn B χ σ (fun _ => -s)
  let σ' : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.segmentFactor (T.segmentFactor (σ i) s) (-s)
  have eσ (i) : σ' i ≅ σ i := by
    apply SmoothRep.mkIso
    change (realPowerTwist (T.determinantNorm (B.size i)) (-s)
      (realPowerTwist (T.determinantNorm (B.size i)) s (σ i).representation)).Equiv _
    rw [realPowerTwist_neg_cancel]
    exact Representation.Equiv.refl _
  let eI := (T.normalizedProductInductionFunctor B).mapIso (Pi.isoMk eσ)
  have eE : T.segmentFactor ((T.normalizedProductInductionFunctor B).obj
      (fun i => T.segmentFactor (σ i) (-s))) s ≅
      (T.normalizedProductInductionFunctor B).obj σ' := by
    apply SmoothRep.mkIso
    exact E
  exact ⟨eI.symm ≪≫ eE.symm⟩

/-- Construct the tempered datum and all fiber and source isomorphisms from
analytic square-integrability at the original blocks' chosen exponents. -/
private theorem groupedTemperedBlocksWithSource
    (n : ℕ) (d : T.SquareIntegrableLanglandsDatum.{max uF uV,uF} n)
    (hsq : letI := T.topology
      ∀ i, T.IsSquareIntegrable
        (T.segmentFactor (d.blocks i) (-d.exponent i)).representation) :
    letI := T.topology
    ∃ (t : T.TemperedLanglandsDatum.{max uF uV,uF} n)
      (q : Fin d.shape.length → Fin t.shape.length),
      Monotone q ∧ Function.Surjective q ∧
      (∀ i, d.exponent i = t.exponent (q i)) ∧
      (∀ j, ∃ (C : BlockShape (t.shape.size j))
        (e : Fin C.length ≃ {i : Fin d.shape.length // q i = j})
        (h : ∀ k, C.size k = d.shape.size (e k).val),
        StrictMono (fun k => (e k).val) ∧
        Nonempty ((T.normalizedProductInductionFunctor.{uF,max uF uV} C).obj
          (fun k => (h k).symm ▸ T.segmentFactor (d.blocks (e k).val)
            (-d.exponent (e k).val)) ≅ t.blocks j)) ∧
      Nonempty (d.induced ≅ t.standardModule) := by
  let := T.topology
  obtain ⟨D, b, q, hb, hq, hsurj, ha, S, e, h, he, hc⟩ :=
    orderedExponentGrouping n d.shape d.exponent d.antitone
  let δ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear (d.shape.size i) F.Carrier) :=
    fun i => T.segmentFactor (d.blocks i) (-d.exponent i)
  have hi (i) : Representation.IsIrreducible (δ i).representation :=
    (isIrreducible_twist_iff _ _).mpr (d.irreducible i)
  have hu (i) : IsUnitarizable (δ i).representation :=
    (d.unitaryExponent i).normalized_unitarizable
  let τ : ∀ j, ∀ k : Fin (S j).length,
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S j).size k) F.Carrier) :=
    fun j k => (h j k).symm ▸ δ (e j k).val
  have hτ (j k) : Representation.IsIrreducible (τ j k).representation ∧
      T.IsSquareIntegrable (τ j k).representation ∧
      IsUnitarizable (τ j k).representation := by
    have transport (r s : ℕ) (hr : r = s)
        (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear s F.Carrier))
        (hA : Representation.IsIrreducible A.representation ∧
          T.IsSquareIntegrable A.representation ∧ IsUnitarizable A.representation) :
        Representation.IsIrreducible (hr.symm ▸ A).representation ∧
          T.IsSquareIntegrable (hr.symm ▸ A).representation ∧
          IsUnitarizable (hr.symm ▸ A).representation := by
      cases hr
      exact hA
    exact transport _ _ (h j k) _ ⟨hi _, hsq _, hu _⟩
  have hI (j) := squareIntegrableBlockInduction.{uF,uV} F T
    (D.size j) (D.positive j) (S j) (τ j) (hτ j)
  let t : T.TemperedLanglandsDatum.{max uF uV,uF} n := {
    shape := D
    blocks := fun j => (T.normalizedProductInductionFunctor.{uF,max uF uV} (S j)).obj (τ j)
    irreducible := fun j => (hI j).1
    tempered := fun j => (hI j).2.2
    exponent := b
    strictAnti := hb }
  refine ⟨t, q, hq, hsurj, ha, ?_, ?_⟩
  · intro j
    exact ⟨S j, e j, h j, he j, ⟨Iso.refl _⟩⟩
  · change Nonempty ((T.normalizedProductInductionFunctor.{uF,max uF uV} d.shape).obj d.blocks ≅
      (T.normalizedProductInductionFunctor.{uF,max uF uV} D).obj
        (fun j => T.segmentFactor (t.blocks j) (b j)))
    let E : ((j : Fin D.length) × Fin (S j).length) ≃ Fin d.shape.length :=
      (Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv q)
    let σ : ∀ j, ∀ k : Fin (S j).length,
        SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((S j).size k) F.Carrier) :=
      fun j k => (h j k).symm ▸ d.blocks (e j k).val
    have hτ' (j k) : T.segmentFactor (σ j k) (-b j) = τ j k := by
      have ha' : d.exponent (e j k).val = b j := by
        rw [ha, (e j k).property]
      dsimp only [τ, δ, σ]
      rw [ha']
      have transport (r s : ℕ) (hr : r = s)
          (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear s F.Carrier)) (c : ℝ) :
          T.segmentFactor (hr.symm ▸ A) c = hr.symm ▸ T.segmentFactor A c := by
        cases hr
        rfl
      exact transport _ _ (h j k) _ _
    have eblock (j) : Nonempty ((T.normalizedProductInductionFunctor.{uF,max uF uV} (S j)).obj (σ j) ≅
        T.segmentFactor (t.blocks j) (b j)) := by
      have hcommon := groupedCommonExponentIso.{uF,max uF uV} F T
        (D.size j) (D.positive j) (S j) (σ j) (b j)
      have hf : (fun k => T.segmentFactor (σ j k) (-b j)) = τ j := funext (hτ' j)
      rw [hf] at hcommon
      exact hcommon
    obtain ⟨ereg⟩ := Parabolic.orderedProductRegrouping.{uF,max uF uV} F T
      n d.shape D S E (fun a => h a.1 a.2) hc d.blocks
    let eblocks := (T.normalizedProductInductionFunctor.{uF,max uF uV} D).mapIso
      (Pi.isoMk fun j => Classical.choice (eblock j))
    refine ⟨ereg ≪≫ ?_⟩
    convert eblocks using 1
    congr 1

/-- Group maximal consecutive equal-exponent runs into genuine irreducible
analytically tempered blocks, with the original induced representation. -/
theorem squareIntegrableEqualExponentGrouping :
    SquareIntegrableEqualExponentGrouping.{uF,uV} F T := by
  let := T.topology
  intro n _ d
  have hsq (i) : T.IsSquareIntegrable
      (T.segmentFactor (d.blocks i) (-d.exponent i)).representation :=
    chosenUnitarySquareIntegrability.{uF,uV} F T
      (d.shape.size i) (d.shape.positive i) (d.blocks i)
      (d.irreducible i) (d.essentiallySquareIntegrable i) (d.unitaryExponent i)
  exact ⟨hsq, groupedTemperedBlocksWithSource.{uF,uV} F T n d hsq⟩

end Langlands.Classification
