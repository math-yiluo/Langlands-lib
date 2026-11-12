import Langlands.Representation.Filtration.SingleSurvivingGrade
import Langlands.Representation.Filtration.Splicing
import Langlands.Representation.Smooth.FiniteLengthGrothendieck

/-! # A short exact sequence from the last grade and a surviving prefix grade -/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV

variable {R : Type uR} [CommRing R] {H : Type uG} [Group H] [TopologicalSpace H]
  {A B C : SmoothRep.{uR, uG, uV} R H} {n : ℕ}

/-- If only one grade in the prefix can survive, the last quotient and that
prefix grade form a short exact sequence with the original smooth object. -/
theorem smooth_shortExact_of_last_and_single_prefix
    (s : ObjectRepFiltration A.obj (n + 1)) (q₀ : Fin n)
    (hB : s.gradedRepresentation q₀.castSucc ≅ B.obj)
    (hC : s.gradedRepresentation (Fin.last n) ≅ C.obj)
    (hz : ∀ q : Fin n, q ≠ q₀ →
      Subsingleton (s.gradedRepresentation q.castSucc)) :
    ∃ (f : B.representation.IntertwiningMap A.representation)
      (g : A.representation.IntertwiningMap C.representation),
      SmoothRep.IsShortExact f g := by
  let X := Discrete.mk PUnit.unit
  let e : s.penultimate.representation X ≅ B.obj :=
    s.initialFiltration.singleSurvivingGradeIsoAt X q₀
      (fun q hq => by
        let _ : Subsingleton ((s.graded q.castSucc).obj X) := hz q hq
        exact (Representation.equivOfIso ((s.prefixGradedIso q).app X)).injective.subsingleton) ≪≫
      (s.prefixGradedIso q₀).app X ≪≫ hB
  let f : B.representation.IntertwiningMap A.representation :=
    (e.inv ≫ s.penultimate.inclusion.app X).hom
  let g : A.representation.IntertwiningMap C.representation :=
    (s.lastProjection.app X ≫ hC.hom).hom
  refine ⟨f, g, ?_, ?_, ?_⟩
  · exact (s.penultimate.inclusion_injective X).comp
      (Representation.equivOfIso e.symm).injective
  · exact (Representation.equivOfIso hC).surjective.comp
      (s.lastProjection_surjective X)
  · have hf : LinearMap.range f.toLinearMap =
        LinearMap.range (s.penultimate.inclusion.app X).hom.toLinearMap := by
      ext a
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨e.inv.hom b, rfl⟩
      · rintro ⟨b, rfl⟩
        obtain ⟨v, rfl⟩ := (Representation.equivOfIso e.symm).surjective b
        exact ⟨v, rfl⟩
    have hg : LinearMap.ker g.toLinearMap =
        LinearMap.ker (s.lastProjection.app X).hom.toLinearMap := by
      ext a
      change hC.hom.hom ((s.lastProjection.app X).hom a) = 0 ↔
        (s.lastProjection.app X).hom a = 0
      constructor
      · intro ha
        apply (Representation.equivOfIso hC).injective
        exact ha.trans (map_zero hC.hom.hom).symm
      · intro ha
        exact (congrArg hC.hom.hom ha).trans (map_zero hC.hom.hom)
    exact hf.trans ((s.range_penultimate_eq_ker_lastProjection X).trans hg.symm)

end Langlands
