import Langlands.Representation.Classification.LanglandsHeadProductSubquotientStatement
import Langlands.Representation.Aubert.LanglandsHeadDuality

/-!
# Tadic's Proposition A.4(ii)

The Langlands head of `a + b` is a subquotient of the normalized product of the
Langlands heads of `a` and `b`. The support-adjusted Aubert operator sends Zelevinsky
labels to Langlands heads and is a ring endomorphism of the graded Grothendieck ring,
so the statement follows from Zelevinsky's Proposition 8.4 for labels.
-/

noncomputable section

namespace Langlands.Classification

open Aubert Aubert.SegmentPolynomialSurjectivity Aubert.LanglandsHeadDuality

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- **Tadic 1986, Proposition A.4(ii).** Every Langlands head of `a + b` is a
subquotient of the normalized product of any Langlands heads of `a` and `b`. -/
theorem langlandsHeadProductSubquotient :
    LanglandsHeadProductSubquotient.{uF, uV} F T := by
  let := T.topology
  intro m n hm hn a b A B P hA hB hP
  have hx := binaryProductExactness.{uF, uV} F T
  have hl := gradedInductionRingLaws F T hx
  let := gradedInductionRing F T hx hl
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  have hAirr := isIrreducible_of_isLanglandsHead F T hA
  have hBirr := isIrreducible_of_isLanglandsHead F T hB
  have hPirr := isIrreducible_of_isLanglandsHead F T hP
  obtain ⟨ca, hca⟩ := exists_isLabel_of_degree F T a (degree_of_isLanglandsHead F T hA)
  obtain ⟨cb, hcb⟩ := exists_isLabel_of_degree F T b (degree_of_isLanglandsHead F T hB)
  obtain ⟨cab, hcab⟩ :=
    exists_isLabel_of_degree F T (a + b) (degree_of_isLanglandsHead F T hP)
  have hdA := gradedAdjustedOperator_label F T hx hl ψ a m ca hca A hAirr hA
  have hdB := gradedAdjustedOperator_label F T hx hl ψ b n cb hcb B hBirr hB
  have hdP := gradedAdjustedOperator_label F T hx hl ψ (a + b) (m + n) cab hcab P hPirr hP
  have h84 := one_le_coeff_label_mul F T hx hl ψ hca hcb hcab
  have hfin := binaryProduct_preservesFiniteLength F T m n A B
    (SmoothRep.hasFiniteLength_of_isIrreducible hAirr)
    (SmoothRep.hasFiniteLength_of_isIrreducible hBirr)
  rw [← coeff_gradedAdjustedOperator F T hdP, gradedAdjustedOperator_mul F T hx hl, hdA, hdB,
    basisClass_irreducibleIsoClass, basisClass_irreducibleIsoClass,
    gradedInclusion_mul_gradedInclusion F T hx hl,
    coeff_gradedInclusion_ofRepresentation F T (m + n) _ hfin P hPirr] at h84
  have hsub : SmoothRep.IsSubquotient P ((T.binaryNormalizedProductFunctor m n).obj (A, B)) :=
    (SmoothRep.compositionMultiplicity_pos_iff_isSubquotient ⟨_, hfin⟩ P hPirr).mp
      (by exact_mod_cast h84)
  rwa [T.binaryNormalizedProductFunctor_of_pos hm hn] at hsub

end Langlands.Classification
