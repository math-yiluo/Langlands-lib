import Langlands.Representation.Aubert.LanglandsHeadDuality
import Langlands.Representation.Smooth.ConstituentSupport

/-! # Actual product constituents under adjusted Aubert duality -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.AdjustedProductConstituents

open PadicField.TopologicalData SmoothRep
open SmoothRep.IrreducibleGrothendieckProof SegmentPolynomialSurjectivity

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Identify a coefficient of actual graded induction with its actual
composition multiplicity, without imposing any label convention. -/
theorem coeff_actualProduct
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) {m n : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier))
      (hA : A.IsIrreducible) (hB : B.IsIrreducible) (hC : C.IsIrreducible)
      (hfin : ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)).HasFiniteLength),
      coeff F T (m + n) (GeneralLinear.irreducibleIsoClass (m + n) F.Carrier C hC)
        (gradedMultiplication F T hx
          (basisClass F T m (GeneralLinear.irreducibleIsoClass m F.Carrier A hA))
          (basisClass F T n (GeneralLinear.irreducibleIsoClass n F.Carrier B hB))) =
        (compositionMultiplicity
          ⟨(T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B), hfin⟩ C : ℤ) := by
  let := T.topology
  intro A B C hA hB hC hfin
  rw [basisClass_irreducibleIsoClass, basisClass_irreducibleIsoClass,
    gradedMultiplication_homogeneous]
  change coeff F T (m + n) _ (gradedInclusion F T (m + n) (binaryProductK0 F T hx m n
    (FiniteLengthGrothendieckGroup.ofObject ⟨A, hasFiniteLength_of_isIrreducible hA⟩)
    (FiniteLengthGrothendieckGroup.ofObject ⟨B, hasFiniteLength_of_isIrreducible hB⟩))) = _
  rw [binaryProductK0_classes]
  change coeff F T (m + n) (GeneralLinear.irreducibleIsoClass (m + n) F.Carrier C hC)
    (gradedInclusion F T (m + n) (GeneralLinear.finiteLengthClass (m + n) F.Carrier
      ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)) hfin)) = _
  exact coeff_gradedInclusion_ofRepresentation F T (m + n) _ hfin C hC

/-- A rankwise equality of actual adjusted classes is also the corresponding
equality of actual graded irreducible basis classes. -/
theorem graded_image_of_actual {n : ℕ} :
    letI := T.topology
    ∀ (A AD : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hA : A.IsIrreducible) (hAD : AD.IsIrreducible),
      adjustedOperator.{uF, uV} F T n
          (GeneralLinear.finiteLengthClass n F.Carrier A (hasFiniteLength_of_isIrreducible hA)) =
        GeneralLinear.finiteLengthClass n F.Carrier AD (hasFiniteLength_of_isIrreducible hAD) →
      gradedAdjustedOperator F T
          (basisClass F T n (GeneralLinear.irreducibleIsoClass n F.Carrier A hA)) =
        basisClass F T n (GeneralLinear.irreducibleIsoClass n F.Carrier AD hAD) := by
  let := T.topology
  intro A AD hA hAD hD
  rw [basisClass_irreducibleIsoClass, basisClass_irreducibleIsoClass,
    gradedAdjustedOperator_homogeneous, hD]

/-- Actual adjusted Aubert duality preserves every composition multiplicity
in the product of supplied irreducible factors. -/
theorem compositionMultiplicity_eq_of_adjusted {m n : ℕ} :
    letI := T.topology
    ∀ (A AD : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (B BD : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (C CD : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier))
      (hA : A.IsIrreducible) (hAD : AD.IsIrreducible)
      (hB : B.IsIrreducible) (hBD : BD.IsIrreducible)
      (hC : C.IsIrreducible) (hCD : CD.IsIrreducible),
      adjustedOperator.{uF, uV} F T m
          (GeneralLinear.finiteLengthClass m F.Carrier A (hasFiniteLength_of_isIrreducible hA)) =
        GeneralLinear.finiteLengthClass m F.Carrier AD (hasFiniteLength_of_isIrreducible hAD) →
      adjustedOperator.{uF, uV} F T n
          (GeneralLinear.finiteLengthClass n F.Carrier B (hasFiniteLength_of_isIrreducible hB)) =
        GeneralLinear.finiteLengthClass n F.Carrier BD (hasFiniteLength_of_isIrreducible hBD) →
      adjustedOperator.{uF, uV} F T (m + n)
          (GeneralLinear.finiteLengthClass (m + n) F.Carrier C (hasFiniteLength_of_isIrreducible hC)) =
        GeneralLinear.finiteLengthClass (m + n) F.Carrier CD (hasFiniteLength_of_isIrreducible hCD) →
      ∀ (hfin : ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)).HasFiniteLength)
        (hfinD : ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (AD, BD)).HasFiniteLength),
        compositionMultiplicity
            ⟨(T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B), hfin⟩ C =
          compositionMultiplicity
            ⟨(T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (AD, BD), hfinD⟩ CD := by
  let := T.topology
  intro A AD B BD C CD hA hAD hB hBD hC hCD hDA hDB hDC hfin hfinD
  let hx := binaryProductExactness.{uF, uV} F T
  have hm := gradedOperator_multiplicative_of_homogeneous F T (adjustedOperator F T) hx
    (adjustedHomogeneousMultiplicativity F T hx)
  have hm' := hm (basisClass F T m (GeneralLinear.irreducibleIsoClass m F.Carrier A hA))
    (basisClass F T n (GeneralLinear.irreducibleIsoClass n F.Carrier B hB))
  change gradedAdjustedOperator F T _ = gradedMultiplication F T hx
    (gradedAdjustedOperator F T _) (gradedAdjustedOperator F T _) at hm'
  rw [graded_image_of_actual F T A AD hA hAD hDA,
    graded_image_of_actual F T B BD hB hBD hDB] at hm'
  have he := LanglandsHeadDuality.coeff_gradedAdjustedOperator F T
    (graded_image_of_actual F T C CD hC hCD hDC)
    (gradedMultiplication F T hx
      (basisClass F T m (GeneralLinear.irreducibleIsoClass m F.Carrier A hA))
      (basisClass F T n (GeneralLinear.irreducibleIsoClass n F.Carrier B hB)))
  rw [hm', coeff_actualProduct F T hx AD BD CD hAD hBD hCD hfinD,
    coeff_actualProduct F T hx A B C hA hB hC hfin] at he
  exact_mod_cast he.symm

/-- Every actual irreducible constituent has an actual adjusted dual
constituent in the product of any supplied adjusted dual factors. -/
theorem exists_adjusted_isSubquotient {m n : ℕ} :
    letI := T.topology
    ∀ (A AD : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (B BD : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier))
      (hA : A.IsIrreducible) (hAD : AD.IsIrreducible)
      (hB : B.IsIrreducible) (hBD : BD.IsIrreducible) (hC : C.IsIrreducible),
      adjustedOperator.{uF, uV} F T m
          (GeneralLinear.finiteLengthClass m F.Carrier A (hasFiniteLength_of_isIrreducible hA)) =
        GeneralLinear.finiteLengthClass m F.Carrier AD (hasFiniteLength_of_isIrreducible hAD) →
      adjustedOperator.{uF, uV} F T n
          (GeneralLinear.finiteLengthClass n F.Carrier B (hasFiniteLength_of_isIrreducible hB)) =
        GeneralLinear.finiteLengthClass n F.Carrier BD (hasFiniteLength_of_isIrreducible hBD) →
      IsSubquotient C ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)) →
      ∃ (CD : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier))
        (hCD : CD.IsIrreducible),
        adjustedOperator.{uF, uV} F T (m + n)
            (GeneralLinear.finiteLengthClass (m + n) F.Carrier C (hasFiniteLength_of_isIrreducible hC)) =
          GeneralLinear.finiteLengthClass (m + n) F.Carrier CD (hasFiniteLength_of_isIrreducible hCD) ∧
        IsSubquotient CD ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (AD, BD)) := by
  let := T.topology
  intro A AD B BD C hA hAD hB hBD hC hDA hDB hsub
  obtain ⟨CD, hCD, hDC⟩ := LanglandsHeadDuality.adjustedOperator_irreducible_eq F T (m + n) C hC
  refine ⟨CD, hCD, hDC, ?_⟩
  have hfin := binaryProduct_preservesFiniteLength F T m n A B
    (hasFiniteLength_of_isIrreducible hA) (hasFiniteLength_of_isIrreducible hB)
  have hfinD := binaryProduct_preservesFiniteLength F T m n AD BD
    (hasFiniteLength_of_isIrreducible hAD) (hasFiniteLength_of_isIrreducible hBD)
  apply (compositionMultiplicity_pos_iff_isSubquotient ⟨_, hfinD⟩ CD hCD).mp
  rw [← compositionMultiplicity_eq_of_adjusted F T A AD B BD C CD
    hA hAD hB hBD hC hCD hDA hDB hDC hfin hfinD]
  exact (compositionMultiplicity_pos_iff_isSubquotient ⟨_, hfin⟩ C hC).mpr hsub

end Langlands.Aubert.AdjustedProductConstituents
