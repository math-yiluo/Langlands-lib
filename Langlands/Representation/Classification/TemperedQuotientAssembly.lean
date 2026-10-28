import Langlands.Representation.Classification.TemperedLanglandsQuotientCoverageStatement
import Langlands.Representation.Classification.TemperedQuotientGLAdapters
import Langlands.Representation.Classification.MaximalConeProof
import Langlands.Representation.Classification.BlockTensorTemperedProof
import Langlands.Representation.Classification.TemperedSmoothDualityStatement
import Langlands.Representation.Classification.UnitaryGenericCompatibilityStatement
import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Twist.SubquotientProof

/-!
# Development assembly of tempered quotient coverage

The two unproved prerequisites remain explicit arguments. This draft is not
the exact coverage proof and must not be submitted as that proof.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear
open scoped BigOperators TensorProduct

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable (T : F.TopologicalData)

/-- A simultaneous real determinant twist of a block tensor is the tensor of
the corresponding twists of its factors. -/
theorem leviRealPowerTwist_blockTensor {n : ℕ} (B : BlockShape n)
    (V : Fin B.length → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (t : Fin B.length → ℝ) :
    T.leviRealPowerTwist B t (B.blockTensor ρ) =
      B.blockTensor (fun i => realPowerTwist (T.determinantNorm (B.size i)) (t i) (ρ i)) := by
  apply MonoidHom.ext
  intro g
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change (T.leviRealPowerCharacter B t g : ℂ) •
      B.blockTensor ρ g (PiTensorProduct.tprod ℂ v) =
    B.blockTensor (fun i => realPowerTwist (T.determinantNorm (B.size i)) (t i) (ρ i))
      g (PiTensorProduct.tprod ℂ v)
  rw [B.blockTensor_tprod, B.blockTensor_tprod]
  simp only [realPowerTwist_apply]
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ]
  congr 1
  simp only [PadicField.TopologicalData.leviRealPowerCharacter_apply,
    Units.coe_prod, coe_realPowerCharacter]

/-- The published quotient adapter expressed using bundled twisted products. -/
theorem gl_exists_surjective_from_reversedTwistedProductDual (n : ℕ)
    (B : BlockShape n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
      π.IsIrreducible →
      ∀ (δ : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
        (s : Fin B.length → ℝ)
        (A : (CuspidalJacquetMultiplicity.oppositeJacquet T B
          (Rep.of π.contragredient.representation)).ρ.IntertwiningMap
          (B.blockTensor (fun i => (T.segmentFactor (δ i) (s i)).representation))),
        A ≠ 0 →
          ∃ q : (smoothContragredient (T.twistedProductInduced B.reverse
              (fun i => δ i.rev) (fun i => s i.rev)).representation).IntertwiningMap
                π.representation,
            Function.Surjective q := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro π hπ δ s A hA
  erw [PadicField.TopologicalData.twistedProductInduced_representation]
  dsimp only [PadicField.TopologicalData.twistedBlocks]
  exact gl_exists_surjective_from_reversedProductDual F T n B π hπ
    (fun i => (T.segmentFactor (δ i) (s i)).obj.V)
    (fun i => (T.segmentFactor (δ i) (s i)).representation)
    (fun i => (T.segmentFactor (δ i) (s i)).isSmooth) A hA

set_option maxHeartbeats 240000 in
/-- Development assembly only: the missing analytic and product duality results
are explicit hypotheses, to be discharged by independently published proofs. -/
theorem temperedLanglandsQuotientCoverage_of
    (hdual : PadicTemperedSmoothDualityStatement.{uF, max uF uV})
    (hproduct : TwistedProductOrdinaryDualClause.{uF, max uF uV} F T) :
    TemperedLanglandsQuotientCoverage.{uF, uV} F T := by
  classical
  let := T.topology
  intro n hn π hπ
  let := T.generalLinearTopologicalGroup n
  have hπa : π.IsAdmissible := (CuspidalSupport.cuspidalEmbedding F T n π hπ).1
  have hπdi : π.contragredient.IsIrreducible :=
    (SmoothRep.isIrreducible_contragredient_iff
      (GeneralLinear.compactOpen_cofinal F T n) π hπa).mpr hπ
  have hπda : π.contragredient.IsAdmissible :=
    (SmoothRep.isAdmissible_contragredient_iff
      (GeneralLinear.compactOpen_cofinal F T n) π).mpr hπa
  obtain ⟨B, χ, r, C, q, t, χC, S,
      _, _, _, _, _, ht, _, _, _, _, _, _, _, hSI, hSA, _, ⟨f, hf⟩, htemp, _⟩ :=
    glMaximalConeJacquetQuotient p F T n hn (Rep.of π.contragredient.representation)
      hπdi hπda
  let := T.leviTopologicalGroup C
  let σ := T.leviRealPowerTwist C (-t) S.ρ
  have hσI : Representation.IsIrreducible σ :=
    (isIrreducible_twist_iff (T.leviRealPowerCharacter C (-t)) S.ρ).mpr hSI
  have hσA : IsAdmissible σ :=
    (isAdmissible_twist_iff (T.leviRealPowerCharacter C (-t)) S.ρ
      (T.isOpen_ker_leviRealPowerCharacter C (-t))).mpr hSA
  obtain ⟨A, hAI, hAA, ⟨e⟩⟩ :=
    CuspidalSupport.padicLeviAdmissibleFactorization p F T n hn C
      (SmoothRep.of σ hσA.1) hσI hσA
  have hAT : ∀ i, T.IsTempered (A i).representation := by
    apply (glBlockTensorTempered p F T n hn C (fun i => (A i).obj.V)
      (fun i => (A i).representation) hAI hAA).mpr
    intro mQ bQ μ hμ
    exact isTemperedModCenter_of_equiv e μ (htemp μ)
  let eS : S.ρ.Equiv
      (C.blockTensor (fun i => (T.segmentFactor (A i) (t i)).representation)) := by
    have et := twistEquiv (T.leviRealPowerCharacter C t) e
    change (T.leviRealPowerTwist C t σ).Equiv
      (T.leviRealPowerTwist C t (C.blockTensor (fun i => (A i).representation))) at et
    dsimp [σ] at et
    rw [T.leviRealPowerTwist_cancel_neg] at et
    rw [leviRealPowerTwist_blockTensor F T C] at et
    exact et
  have hf0 : f ≠ 0 := by
    let : Nontrivial S.V := by
      let := hSI
      exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (C.Levi F.Carrier)) S.ρ.asModule
    intro hz
    obtain ⟨v, hv⟩ := exists_ne (0 : S.V)
    obtain ⟨w, hw⟩ := hf v
    apply hv
    rw [← hw, hz]
    rfl
  let fA := eS.toIntertwiningMap.comp f
  have hfA : fA ≠ 0 := by
    intro hz
    apply hf0
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    apply eS.injective
    have hw := congrArg (fun k => k w) hz
    change eS (f w) = 0 at hw
    change eS (f w) = eS 0
    simpa only [map_zero] using hw
  obtain ⟨Q, hQ⟩ := gl_exists_surjective_from_reversedTwistedProductDual F T n C π hπ
    A t fA hfA
  let δ : ∀ i : Fin C.reverse.length,
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (C.reverse.size i) F.Carrier) :=
    fun i => A i.rev
  let (i : Fin C.reverse.length) := T.generalLinearTopologicalGroup (C.reverse.size i)
  let δv : ∀ i : Fin C.reverse.length,
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (C.reverse.size i) F.Carrier) :=
    fun i => (δ i).contragredient
  obtain ⟨E⟩ := hproduct n hn C.reverse δ (fun i => t i.rev) (fun i => hAA i.rev)
  let qd := Q.comp E.symm.toIntertwiningMap
  have hqd : Function.Surjective qd := hQ.comp E.symm.surjective
  let d : T.TemperedLanglandsDatum.{max uF uV, uF} n :=
    { shape := C.reverse
      blocks := δv
      irreducible := fun i =>
        (SmoothRep.isIrreducible_contragredient_iff
          (GeneralLinear.compactOpen_cofinal F T (C.reverse.size i))
          (δ i) (hAA i.rev)).mpr (hAI i.rev)
      tempered := fun i =>
        (hdual p F T (C.reverse.size i) (C.reverse.positive i)
          (δ i).obj.V (δ i).representation (hAA i.rev)).mpr (hAT i.rev)
      exponent := fun i => -t i.rev
      strictAnti := strictAnti_neg_reverse ht }
  refine ⟨d, ?_⟩
  change IsIrreducibleQuotient
    (T.twistedProductInduced C.reverse δv (fun i => -t i.rev)).representation
    π.representation
  exact ⟨hπ, qd, hqd⟩

/-- An actual tempered datum and its quotient property, conditional on the two
remaining independent duality statements. -/
def temperedLanglandsQuotientWitnessOfDuality
    (hdual : PadicTemperedSmoothDualityStatement.{uF, max uF uV})
    (hproduct : TwistedProductOrdinaryDualClause.{uF, max uF uV} F T) :
    letI := T.topology
    ∀ (n : ℕ) (_hn : 0 < n)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      π.IsIrreducible →
        {d : T.TemperedLanglandsDatum.{max uF uV, uF} n // d.IsLanglandsQuotient π} := by
  let := T.topology
  intro n hn π hπ
  have h := temperedLanglandsQuotientCoverage_of F T hdual hproduct n hn π hπ
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

end Langlands.Classification
