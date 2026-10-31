import Langlands.Representation.Classification.SegmentConstituentStatement
import Langlands.Representation.Classification.CommonImageMultiplicityOneProof
import Langlands.Representation.Classification.SegmentJacquetMultiplicityProof
import Langlands.Representation.Classification.CuspidalJacquetMultiplicityProof
import Langlands.Representation.Classification.SegmentJacquetReversal
import Langlands.Representation.Classification.SegmentTensorReversalProof
import Langlands.Representation.Classification.SegmentInductionAdmissibilityProof
import Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessProof
import Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionProof
import Langlands.Representation.Classification.OppositeJacquetQuotientDetectionProof
import Langlands.Representation.CuspidalSupport.AssociationForwardHomProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Group.GL.CompactOpen

/-! Strong increasing socle and decreasing head of an individual segment. -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData CategoryTheory
open CuspidalJacquetMultiplicity CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem segmentQuotient_admissible (n : ℕ) :
    letI := T.topology
    ∀ (A P : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      (q : A ⟶ P),
      Function.Surjective (SmoothRep.hom q) →
      IsAdmissible A.representation → IsAdmissible P.representation := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A P q hq hA
  have hcofinal : ∀ K : OpenSubgroup (GeneralLinear n F.Carrier),
      ∃ L : OpenSubgroup (GeneralLinear n F.Carrier),
        IsCompact (L : Set (GeneralLinear n F.Carrier)) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLc, hLK⟩ :=
      T.generalLinearCompactOpen n K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L, hLc, hLK⟩
  exact Unramified.SphericalExistence.isAdmissible_of_surjective
    hcofinal (SmoothRep.hom q) hq hA

/-- A two-sided constituent for every actual representative gives the exact
segment target, including its universal reverse-head clause. -/
private theorem segmentZelevinskyConstituentExistence_of_pointwise
    (hpoint :
      letI := T.topology
      ∀ {r : ℕ} (m : ℕ), 0 < m → ∀ (hr : 0 < r)
        (A : SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r)),
        ∃ π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (m * r) F.Carrier),
          IsIrreducibleSocle (T.segmentInduced A.obj m hr).representation
            π.representation ∧
          IsIrreducibleHead (T.segmentInducedDown A.obj m hr).representation
            π.representation) :
    SegmentZelevinskyConstituentExistence.{uF,uV} F T := by
  let := T.topology
  intro Δ
  obtain ⟨A, hA⟩ := Quotient.exists_rep Δ.base.cls
  have hA' : Δ.base.IsRepresentedBy A := hA
  obtain ⟨π, hsocle, hhead⟩ := hpoint Δ.length Δ.length_pos Δ.rank_pos A
  refine ⟨π, ⟨A, hA', hsocle⟩, ?_⟩
  intro A' hA''
  exact hhead.of_equiv
    (SmoothRep.equivOfIso (T.segmentInducedDownIsoOfRepresented hA' hA'' Δ.length))

/-- Every segment has a strong irreducible increasing socle that is also the
strong decreasing head for every actual representative of its base. -/
theorem segmentZelevinskyConstituentExistence :
    SegmentZelevinskyConstituentExistence.{uF,uV} F T := by
  apply segmentZelevinskyConstituentExistence_of_pointwise F T
  let := T.topology
  intro r m hm hr A
  let := T.generalLinearTopologicalGroup (m * r)
  let B := BlockShape.uniform m r hr
  let σ := FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)
  let τ := FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj m hr)
  let Iu := T.segmentInduced A.obj m hr
  let Id := T.segmentInducedDown A.obj m hr
  let J := upperFunctor.{uF,max uF uV} T B
  have hσ := segmentFactors_isIrreducible_isLeviCuspidal F T m hm hr A
  have hτ := segmentFactorsDown_isIrreducible_isLeviCuspidal F T m hm hr A
  have hseries := segmentJacquetMultiplicityReduction F T
    glCuspidalJacquetMultiplicityPrerequisites.{uF,uV,uV} m hm hr A
  have hadm := segmentInductionAdmissibility F T m hr A.obj A.property.2.1
  have hId : HasJordanHolderMultiplicity (J.obj Id) σ.obj 1 :=
    (segment_upper_opposite_multiplicity_iff T m hr A.obj Id.obj 1).mpr
      hseries.2.2.2
  have hIu : HasJordanHolderMultiplicity (J.obj Iu) σ.obj 1 := hseries.1
  have hqpos : ∀ (P : SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear (m * r) F.Carrier)) (q : Id ⟶ P),
      Function.Surjective (SmoothRep.hom q) → q ≠ 0 →
        ∃ k, HasJordanHolderMultiplicity (J.obj P) σ.obj k ∧ 0 < k := by
    intro P q hq hq0
    have hq0' : SmoothRep.hom q ≠ 0 := by
      intro he
      apply hq0
      exact congrArg SmoothRep.ofHom he
    have hP := segmentQuotient_admissible F T (m * r) Id P q hq hadm.2.2.2
    obtain ⟨k, hk, hkpos, _⟩ := oppositeJacquetQuotientDetection
      p F T (m * r) (Nat.mul_pos hm hr)
      B τ.obj hτ.1 hadm.2.1 P.obj hP (SmoothRep.hom q) hq hq0' 1 hseries.2.2.2
    exact ⟨k, (segment_upper_opposite_multiplicity_iff T m hr A.obj P.obj k).mpr hk,
      hkpos⟩
  have hjpos : ∀ (P : SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear (m * r) F.Carrier)) (j : P ⟶ Iu),
      Function.Injective (SmoothRep.hom j) → j ≠ 0 →
        ∃ k, HasJordanHolderMultiplicity (J.obj P) σ.obj k ∧ 0 < k := by
    intro P j hj hj0
    have hj0' : SmoothRep.hom j ≠ 0 := by
      intro he
      apply hj0
      exact congrArg SmoothRep.ofHom he
    obtain ⟨k, hk, hkpos, _⟩ := upperJacquetSubrepresentationDetection
      p F T (m * r) B σ.obj hσ.1 P.obj (SmoothRep.hom j) hj hj0' 1 hseries.1
    exact ⟨k, hk, hkpos⟩
  have hassoc := (segmentFactors_associated_segmentFactorsDown F T m hr A.obj).symm
  obtain ⟨f, hf⟩ := associatedCuspidalInductionHomTheorem.{uF,uV,uV}
    p F T (m * r) (Nat.mul_pos hm hr) B B τ σ
    hτ.1 hτ.2 hσ.1 hσ.2 hassoc
  let f' : Id ⟶ Iu := SmoothRep.ofHom f
  have hf' : f' ≠ 0 := by
    intro he
    apply hf
    exact congrArg SmoothRep.hom he
  obtain ⟨P, q, j, _, _, _, hhead, hsocle⟩ := commonImageMultiplicityOne
    (GeneralLinear (m * r) F.Carrier) (B.Levi F.Carrier)
    J Id Iu σ.obj hId hIu hqpos hjpos f' hf'
  exact ⟨P, hsocle, hhead⟩

end Langlands.Classification
