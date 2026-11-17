import Langlands.Geometry.Analytic.AffinoidFieldCharacters
import Langlands.Geometry.Analytic.SmallAffinoidSpectrum

/-! # Full field points of small actual affinoid pushouts -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory Limits Set PresentedAffinoidAlgebra
open AffinoidAtlasPresentation SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]

private def wholeIndex (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)] :
    (saturated R).presentation.atlas.Index :=
  (presentation R).atlas.originalSaturatedIndex PUnit.unit

private theorem wholeRange (R : PresentedAffinoidAlgebra K)
    [Small.{v} (BanachSpectrum R)] :
    range ((saturated R).presentation.atlas.chart (wholeIndex R)) = univ :=
  ((presentation R).atlas.saturatedAtlas_original_range PUnit.unit).trans
    (spectrumHomeomorph R).surjective.range_eq

private theorem wholeAlgebra (R : PresentedAffinoidAlgebra K)
    [Small.{v} (BanachSpectrum R)] :
    (saturated R).presentation.atlas.algebra (wholeIndex R) = R :=
  (presentation R).atlas.saturatedAtlas_original_algebra PUnit.unit

private def characterCast {R S : PresentedAffinoidAlgebra K} (h : R = S) :
    BoundedAlgHom K R L ≃ BoundedAlgHom K S L :=
  Equiv.cast (congrArg (fun T : PresentedAffinoidAlgebra K => BoundedAlgHom K T L) h)

/-- Full field points of the actual small saturated spectrum are bounded
characters of its original algebra, conditional on domain residue comparison. -/
def fieldPointCharacterEquiv (R : PresentedAffinoidAlgebra K)
    [Small.{v} (BanachSpectrum R)]
    (hd : DomainCompletedResidueSurjectivityStatement.{u}) :
    FieldPoint L (saturated R).presentation ≃ BoundedAlgHom K R L :=
  (FieldPoint.globalChartCharacterEquiv hd (wholeIndex R) (wholeRange R)).trans
    (characterCast (wholeAlgebra R))

omit [CompleteSpace K] [CompleteSpace L] in
private theorem characterCast_comp {R S R' S' : PresentedAffinoidAlgebra K}
    (hR : R' = R) (hS : S' = S)
    (f' : BoundedAlgHom K R' S') (f : BoundedAlgHom K R S)
    (hf : HEq f' f) (c : BoundedAlgHom K S' L) :
    characterCast hR (c.comp f') = (characterCast hS c).comp f := by
  cases hR
  cases hS
  cases eq_of_heq hf
  rfl

/-- The equivalence computes the actual full field-point map by
precomposition with the original bounded algebra map. -/
theorem fieldPointCharacterEquiv_map
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    {R S : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
    (f : BoundedAlgHom K R S) (p : FieldPoint L (saturated S).presentation) :
    fieldPointCharacterEquiv R hd (p.map (map f) (saturated S).hasAllLocalDomains) =
      (fieldPointCharacterEquiv S hd p).comp f := by
  have h : (strongMap f).baseMap '' range ((presentation S).atlas.chart PUnit.unit) ⊆
      range ((presentation R).atlas.chart PUnit.unit) := by
    intro x _
    exact ⟨(spectrumHomeomorph R).symm x, (spectrumHomeomorph R).apply_symm_apply x⟩
  have hsat := (strongMap f).saturationExtension_original_admissible
    PUnit.unit PUnit.unit h
  have he := p.map_boundedEval (map f) (saturated S).hasAllLocalDomains
    (wholeIndex R) ((wholeRange R).symm ▸ mem_univ _)
    (wholeIndex S) ((wholeRange S).symm ▸ mem_univ _) hsat
  change characterCast (wholeAlgebra R)
      ((p.map (map f) (saturated S).hasAllLocalDomains).boundedEval
        (wholeIndex R) ((wholeRange R).symm ▸ mem_univ _)) =
    (characterCast (wholeAlgebra S)
      (p.boundedEval (wholeIndex S) ((wholeRange S).symm ▸ mem_univ _))).comp f
  rw [he]
  exact characterCast_comp (wholeAlgebra R) (wholeAlgebra S) _ f
    ((strongMap f).saturationExtension_pullback_original
      (strongMap_coherent f) PUnit.unit PUnit.unit h) _

section Pushout

variable [IsUltrametricDist L]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)
  [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)]
  [Small.{v} (BanachSpectrum C)]
  [Small.{v} (BanachSpectrum (AffinoidPushout.algebra f g))]

/-- The actual full field-point functor sends an actual small affinoid
pushout square to a pullback, conditional on domain residue comparison. -/
theorem pushout_fieldPoint_isPullback
    (hd : DomainCompletedResidueSurjectivityStatement.{u}) :
    IsPullback ((fieldPointFunctor L).map (map (AffinoidPushout.leftMap f g)))
      ((fieldPointFunctor L).map (map (AffinoidPushout.rightMap f g)))
      ((fieldPointFunctor L).map (map f)) ((fieldPointFunctor L).map (map g)) := by
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · rw [← Functor.map_comp, ← Functor.map_comp, ← map_comp, ← map_comp,
      AffinoidPushout.condition]
  · intro p q hpq
    apply (fieldPointCharacterEquiv (AffinoidPushout.algebra f g) hd).injective
    apply AffinoidPushout.hom_ext f g L
    · exact (fieldPointCharacterEquiv_map hd (AffinoidPushout.leftMap f g) p).symm.trans
        ((congrArg (fieldPointCharacterEquiv B hd) hpq.1).trans
          (fieldPointCharacterEquiv_map hd (AffinoidPushout.leftMap f g) q))
    · exact (fieldPointCharacterEquiv_map hd (AffinoidPushout.rightMap f g) p).symm.trans
        ((congrArg (fieldPointCharacterEquiv C hd) hpq.2).trans
          (fieldPointCharacterEquiv_map hd (AffinoidPushout.rightMap f g) q))
  · intro p q hpq
    have hc : (fieldPointCharacterEquiv B hd p).comp f =
        (fieldPointCharacterEquiv C hd q).comp g :=
      (fieldPointCharacterEquiv_map hd f p).symm.trans
        ((congrArg (fieldPointCharacterEquiv A hd) hpq).trans
          (fieldPointCharacterEquiv_map hd g q))
    obtain ⟨c, hc, -⟩ := AffinoidPushout.existsUnique_lift f g L
      (fieldPointCharacterEquiv B hd p) (fieldPointCharacterEquiv C hd q) hc
    let r := (fieldPointCharacterEquiv (AffinoidPushout.algebra f g) hd).symm c
    have hr : fieldPointCharacterEquiv (AffinoidPushout.algebra f g) hd r = c :=
      (fieldPointCharacterEquiv (AffinoidPushout.algebra f g) hd).apply_symm_apply c
    refine ⟨r, ?_, ?_⟩
    · apply (fieldPointCharacterEquiv B hd).injective
      exact (fieldPointCharacterEquiv_map hd (AffinoidPushout.leftMap f g) r).trans
        ((congrArg (fun e : BoundedAlgHom K (AffinoidPushout.algebra f g) L =>
          e.comp (AffinoidPushout.leftMap f g)) hr).trans hc.1)
    · apply (fieldPointCharacterEquiv C hd).injective
      exact (fieldPointCharacterEquiv_map hd (AffinoidPushout.rightMap f g) r).trans
        ((congrArg (fun e : BoundedAlgHom K (AffinoidPushout.algebra f g) L =>
          e.comp (AffinoidPushout.rightMap f g)) hr).trans hc.2)

/-- The same pullback is expressed using the actual descended full
field-point functor and the original localization functor. -/
theorem pushout_localizedFieldPoint_isPullback
    (hd : DomainCompletedResidueSurjectivityStatement.{u}) :
    IsPullback
      ((localizedFieldPointFunctor L).map
        (localizationFunctor.map (map (AffinoidPushout.leftMap f g))))
      ((localizedFieldPointFunctor L).map
        (localizationFunctor.map (map (AffinoidPushout.rightMap f g))))
      ((localizedFieldPointFunctor L).map (localizationFunctor.map (map f)))
      ((localizedFieldPointFunctor L).map (localizationFunctor.map (map g))) := by
  change IsPullback
    ((localizationFunctor ⋙ localizedFieldPointFunctor L).map
      (map (AffinoidPushout.leftMap f g)))
    ((localizationFunctor ⋙ localizedFieldPointFunctor L).map
      (map (AffinoidPushout.rightMap f g)))
    ((localizationFunctor ⋙ localizedFieldPointFunctor L).map (map f))
    ((localizationFunctor ⋙ localizedFieldPointFunctor L).map (map g))
  rw [localizationFunctor_localizedFieldPointFunctor]
  exact pushout_fieldPoint_isPullback f g hd

end Pushout

end Langlands.Analytic.SmallAffinoidSpectrum
