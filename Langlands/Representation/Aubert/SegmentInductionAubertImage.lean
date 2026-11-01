import Langlands.Representation.Aubert.SegmentJacquetDetection
import Langlands.Representation.Aubert.QuasicuspidalInductionSupport
import Langlands.Representation.Aubert.QuasicuspidalJacquetExchange
import Langlands.Representation.Aubert.InvolutivityProof

/-! Signed effectivity and actual irreducible images on segment induction support. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Parabolic CuspidalSupport Classification SegmentFullJacquet
open SmoothRep.IrreducibleGrothendieckProof SmoothRep.IrreducibleOperator
open VirtualRepresentation

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

set_option maxHeartbeats 3200000 in
/-- The support-dependent sign of the actual Aubert image is effective on
every actual irreducible subquotient of an increasing segment induction. -/
theorem segmentInductionAubert_effective (m r : ℕ) (hm : 0 < m) (hr : 0 < r) :
    letI := T.topology
    ∀ (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := r))
      (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier))
      (hC : C.IsIrreducible),
      SmoothRep.IsSubquotient C (T.segmentInduced A.obj m hr) →
      factorMap ((((-1 : ℤ) ^ (m * r - m)) •
        alternatingOperator.{uF, uV} F T (m * r))
          (GeneralLinear.finiteLengthClass (m * r) F.Carrier C
            (SmoothRep.hasFiniteLength_of_isIrreducible hC))) ∈ effective := by
  let := T.topology
  intro A C hC hsub
  let B := BlockShape.uniform m r hr
  let σ := FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)
  let I := T.segmentInduced A.obj m hr
  have hσ := segmentFactors_isIrreducible_isLeviCuspidal F T m hm hr A
  let hσfl := SmoothRep.hasFiniteLength_of_isIrreducible hσ.1
  let hI := normalizedInductionK0_hasFiniteLength.{uF, uV} F T B σ hσfl
  let v := compositionFactors ⟨I, hI⟩
  let D := alternatingOperator.{uF, uV} F T (m * r)
  let s : ℤ := (-1 : ℤ) ^ (m * r - m)
  have hs : s = 1 ∨ s = -1 := neg_one_pow_eq_or ℤ _
  have hss : s * s = 1 := by
    rcases hs with hs | hs <;> rw [hs] <;> norm_num
  let xC := GeneralLinear.finiteLengthClass (m * r) F.Carrier C
    (SmoothRep.hasFiniteLength_of_isIrreducible hC)
  let w := factorMap ((s • D) xC)
  have hV : factorMap (normalizedInductionK0.{uF, uV} F T B
      (B.finiteLengthClass F.Carrier σ hσfl)) = v := by
    rw [normalizedInductionK0_finiteLengthClass F T B σ hσfl hI]
    exact factorMap_ofRepresentation _ _
  have hc : SmoothRep.irreducibleIsoClass C hC ∈ v.support :=
    (mem_support_compositionFactors_iff_isSubquotient ⟨I, hI⟩ C hC).mpr hsub
  have hDfactor : onIrreducibles D (generator (SmoothRep.irreducibleIsoClass C hC)) =
      factorMap (D xC) := by
    change factorMap (D (SmoothRep.realizeIrreducibles ℂ
      (GeneralLinear (m * r) F.Carrier)
        (generator (SmoothRep.irreducibleIsoClass C hC)))) = _
    rw [SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass C hC
      (SmoothRep.hasFiniteLength_of_isIrreducible hC)]
    rfl
  have hDsupport :
      (onIrreducibles D (generator (SmoothRep.irreducibleIsoClass C hC))).support ⊆
        v.support := by
    have h := (quasicuspidalInductionSupport.{uF, uV} F T (m * r)
      (Nat.mul_pos hm hr) B σ hσfl hσ.2.2).2
    rw [hV] at h
    exact h _ hc
  have hw : w.support ⊆ v.support := by
    change (factorMap ((s • D) xC)).support ⊆ v.support
    rw [LinearMap.smul_apply, map_smul]
    exact Finsupp.support_smul.trans (by rw [← hDfactor]; exact hDsupport)
  have hqc := inductionJacquet_subquotient_isLeviQuasicuspidal.{uF, uV}
    F T B σ hσ.2.2 C hsub
  have hqcRev : IsLeviQuasicuspidal B.reverse
      ((T.normalizedJacquetFunctor B.reverse).obj C).representation := by
    change IsLeviQuasicuspidal B
      ((T.normalizedJacquetFunctor B.reverse).obj C).representation
    rw [uniformJacquetObject_reverse_eq F T hr C]
    exact hqc
  have hExchange := quasicuspidalJacquetExchange.{uF, uV} F T (m * r) B C
    (SmoothRep.hasFiniteLength_of_isIrreducible hC) hqcRev
  have hJw : jacquetOnIrreducibles.{uF, uV} F T B w ∈ effective := by
    change jacquetOnIrreducibles F T B (factorMap ((s • D) xC)) ∈ effective
    rw [jacquetOnIrreducibles_factorMap, LinearMap.smul_apply, map_smul]
    change factorMap (s • normalizedJacquetK0 F T B (D xC)) ∈ effective
    change normalizedJacquetK0 F T B (D xC) =
      s • B.finiteLengthClass F.Carrier (reversedJacquetObject F T B C) _ at hExchange
    rw [hExchange, smul_smul, hss, one_smul]
    rw [BlockShape.finiteLengthClass, factorMap_ofRepresentation]
    exact compositionFactors_effective _
  exact segmentJacquetDetection.{uF, uV} F T m r hm hr A w hw hJw

/-- Actual irreducible subquotients of one increasing segment induction
have actual irreducible Aubert images up to sign. -/
def SegmentInductionAubertImageStatement : Prop :=
  letI := T.topology
  ∀ (m r : ℕ) (_hm : 0 < m) (hr : 0 < r)
    (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := r))
    (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier))
    (hC : C.IsIrreducible),
    SmoothRep.IsSubquotient C (T.segmentInduced A.obj m hr) →
    ∃ (Q : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier))
      (hQ : Q.IsIrreducible),
      alternatingOperator.{uF, uV} F T (m * r)
          (GeneralLinear.finiteLengthClass (m * r) F.Carrier C
            (SmoothRep.hasFiniteLength_of_isIrreducible hC)) =
        GeneralLinear.finiteLengthClass (m * r) F.Carrier Q
          (SmoothRep.hasFiniteLength_of_isIrreducible hQ) ∨
      alternatingOperator.{uF, uV} F T (m * r)
          (GeneralLinear.finiteLengthClass (m * r) F.Carrier C
            (SmoothRep.hasFiniteLength_of_isIrreducible hC)) =
        -GeneralLinear.finiteLengthClass (m * r) F.Carrier Q
          (SmoothRep.hasFiniteLength_of_isIrreducible hQ)

set_option maxHeartbeats 3200000 in
theorem segmentInductionAubertImage :
    SegmentInductionAubertImageStatement.{uF, uV} F T := by
  let := T.topology
  intro m r hm hr A C hC hsub
  let B := BlockShape.uniform m r hr
  let σ := FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)
  let I := T.segmentInduced A.obj m hr
  have hσ := segmentFactors_isIrreducible_isLeviCuspidal F T m hm hr A
  let hσfl := SmoothRep.hasFiniteLength_of_isIrreducible hσ.1
  let hI := normalizedInductionK0_hasFiniteLength.{uF, uV} F T B σ hσfl
  let D := alternatingOperator.{uF, uV} F T (m * r)
  let s : ℤ := (-1 : ℤ) ^ (m * r - m)
  have hs : s = 1 ∨ s = -1 := neg_one_pow_eq_or ℤ _
  have hss : s * s = 1 := by
    rcases hs with hs | hs <;> rw [hs] <;> norm_num
  have hD : Function.Involutive D := by
    intro x
    exact LinearMap.congr_fun (involutivity.{uF, uV} F T (m * r)) x
  have hfix : (s • D)
      (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation I hI) =
        SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation I hI := by
    have h := alternatingOperator_normalizedInductionK0_quasicuspidal.{uF, uV}
      F T B σ hσfl hσ.2.2
    rw [normalizedInductionK0_finiteLengthClass F T B σ hσfl hI] at h
    change D (GeneralLinear.finiteLengthClass (m * r) F.Carrier I hI) =
      s • GeneralLinear.finiteLengthClass (m * r) F.Carrier I hI at h
    change s • D (GeneralLinear.finiteLengthClass (m * r) F.Carrier I hI) =
      GeneralLinear.finiteLengthClass (m * r) F.Carrier I hI
    rw [h, smul_smul, hss, one_smul]
  exact exists_irreducible_image_of_effective_fixed_class D hD.injective s hs
    ⟨I, hI⟩ hfix (fun Q hQ hsubQ =>
      segmentInductionAubert_effective.{uF, uV} F T m r hm hr A Q hQ hsubQ) C hC hsub

end Langlands.Aubert
