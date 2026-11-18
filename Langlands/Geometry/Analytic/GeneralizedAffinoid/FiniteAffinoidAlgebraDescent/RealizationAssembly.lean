import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.SpectrumRealization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.Statement

/-! # Assembling effective finite affinoid algebra realizations -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace BoundedAlgHom.IsFiniteBanach

variable {K : Type u} {A : Type v} {B : Type w} {C : Type z}
  [NormedField K] [NormedCommRing A] [NormedCommRing B] [NormedCommRing C]
  [NormedAlgebra K A] [NormedAlgebra K B] [NormedAlgebra K C]

/-- Bounded target transport preserves the uniform norm control on finite
coefficient lifts, including over trivially normed coefficient fields. -/
theorem postcomp_equiv {f : BoundedAlgHom K A B} (hf : f.IsFiniteBanach)
    (e : BoundedAlgEquiv K B C) : (e.toBoundedAlgHom.comp f).IsFiniteBanach := by
  obtain ⟨n, b, M, hM, hb⟩ := hf
  obtain ⟨D, hD, he⟩ := e.symm.bounded
  refine ⟨n, fun i => e (b i), M * D, mul_pos hM hD, fun y => ?_⟩
  obtain ⟨c, hc, hcn⟩ := hb (e.symm y)
  refine ⟨c, ?_, ?_⟩
  · calc
      (e.toBoundedAlgHom.comp f).coefficientMap (fun i => e (b i)) c =
          e (f.coefficientMap b c) := by
        change ∑ i, e.toAlgEquiv (f (c i)) * e.toAlgEquiv (b i) =
          e.toAlgEquiv (∑ i, f (c i) * b i)
        simp only [map_sum, map_mul]
      _ = y := by rw [hc, e.apply_symm_apply]
  · calc
      ‖c‖ ≤ M * ‖e.symm y‖ := hcn
      _ ≤ M * (D * ‖y‖) := mul_le_mul_of_nonneg_left (he y) hM.le
      _ = (M * D) * ‖y‖ := (mul_assoc M D ‖y‖).symm

end BoundedAlgHom.IsFiniteBanach

namespace PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}
  {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}

namespace MatchingPresentation

variable {t : PairTransitions F} (P : MatchingPresentation t)

/-- Norm-controlled finiteness in the actual matching norm transports to the
presented realization through its bounded inverse. -/
theorem finite_baseMap (hf : t.structuralMap.IsFiniteBanach) :
    P.baseMap.IsFiniteBanach :=
  hf.postcomp_equiv P.equiv.symm

/-- Norm-controlled finiteness in the presented norm transports back to the
original complete matching algebra through the forward bound. -/
theorem finite_matching (hf : P.baseMap.IsFiniteBanach) :
    t.structuralMap.IsFiniteBanach := by
  have h := hf.postcomp_equiv P.equiv
  have hmap : P.equiv.toBoundedAlgHom.comp P.baseMap = t.structuralMap := by
    apply BoundedAlgHom.ext
    intro r
    exact P.equiv.apply_symm_apply _
  rwa [hmap] at h

theorem finite_baseMap_iff :
    P.baseMap.IsFiniteBanach ↔ t.structuralMap.IsFiniteBanach :=
  ⟨P.finite_matching, P.finite_baseMap⟩

end MatchingPresentation

/-- The finite matching bound and canonical original bounded comparisons
supply all remaining effectiveness fields, including both global finite
Banach conditions and the entire quotient-spectrum homeomorphism. -/
def effectiveRealizationOfComparisons (d : DescentData F)
    (P : MatchingPresentation d.toPairTransitions)
    (hf : d.toPairTransitions.structuralMap.IsFiniteBanach)
    (e : ∀ i, BoundedAlgEquiv K (P.originalBaseChange i) (F.algebra i))
    (he : ∀ i, (e i).toBoundedAlgHom = P.comparison i) : EffectiveRealization d where
  toMatchingPresentation := P
  finite_matching := hf
  finite := P.finite_baseMap hf
  comparisonEquiv := e
  comparison_eq := he
  overlap_compatible := P.overlapCompatible
  spectrumEquiv := P.spectrumEquivOfComparison e he
  spectrumEquiv_eq := P.spectrumEquivOfComparison_eq e he
  localSpectrumEquiv i := P.localSpectrumEquivOfComparison i (e i)
  localSpectrumEquiv_eq i := P.localSpectrumEquivOfComparison_eq i (e i) (he i)

@[simp] theorem effectiveRealizationOfComparisons_toMatchingPresentation
    (d : DescentData F) (P : MatchingPresentation d.toPairTransitions)
    (hf : d.toPairTransitions.structuralMap.IsFiniteBanach)
    (e : ∀ i, BoundedAlgEquiv K (P.originalBaseChange i) (F.algebra i))
    (he : ∀ i, (e i).toBoundedAlgHom = P.comparison i) :
    (effectiveRealizationOfComparisons d P hf e he).toMatchingPresentation = P := rfl

end PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent
end Langlands.Analytic
