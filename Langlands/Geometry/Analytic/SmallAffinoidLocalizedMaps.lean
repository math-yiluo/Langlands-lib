import Langlands.Geometry.Analytic.SaturatedTopChartComparison
import Langlands.Geometry.Analytic.QuotientTopTargetHom

/-! # Full localized morphisms between small affinoid spectra -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory PresentedAffinoidAlgebra SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
private theorem exists_heq_boundedAlgHom
    {R S R' S' : PresentedAffinoidAlgebra K} (hR : R' = R) (hS : S' = S)
    (f : BoundedAlgHom K R' S') :
    ∃ g : BoundedAlgHom K R S, HEq g f := by
  subst R' S'
  exact ⟨f, HEq.rfl⟩

variable {R S : PresentedAffinoidAlgebra K}
  [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]

private theorem map_bijective :
    Function.Bijective (fun f : BoundedAlgHom K R S => map.{u, v} f) := by
  constructor
  · intro f g hfg
    change map.{u, v} f = map.{u, v} g at hfg
    have hf := map_pullbackAtTop_heq.{u, v} f
    rw [hfg] at hf
    exact eq_of_heq (hf.symm.trans (map_pullbackAtTop_heq.{u, v} g))
  · intro h
    obtain ⟨f, hf⟩ :=
      exists_heq_boundedAlgHom (top_algebra R) (top_algebra S)
        (h.pullbackAtTop (topIndex R) (top_contains R) (topIndex S))
    refine ⟨f, hom_ext_topAlgebra (topIndex S) (topIndex R)
      (top_contains S) (top_contains R) ?_⟩
    exact eq_of_heq ((map_pullbackAtTop_heq.{u, v} f).trans hf)

private theorem localizedMap_bijective :
    Function.Bijective
      (fun f : BoundedAlgHom K R S => localizationFunctor.map (map.{u, v} f)) := by
  constructor
  · intro f g h
    exact map_bijective.1 (localizationFunctor_map_injective h)
  · intro φ
    obtain ⟨g, hg⟩ := SourceCategory.strongFunctor_map_surjective_of_top
      (A := saturated S) (topIndex R) (top_contains R) (sourceHomEquiv.symm φ)
    obtain ⟨f, rfl⟩ := map_bijective.2 g
    change sourceHomEquiv.symm (localizationFunctor.map (map f)) =
      sourceHomEquiv.symm φ at hg
    exact ⟨f, sourceHomEquiv.symm.injective hg⟩

/-- Actual localized arrows between small affinoid spectra are exactly the
bounded algebra maps in the opposite direction. -/
def localizedMapEquiv (R S : PresentedAffinoidAlgebra K)
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)] :
    BoundedAlgHom K R S ≃
      (localizationFunctor.obj (saturated S) ⟶ localizationFunctor.obj (saturated R)) :=
  Equiv.ofBijective _ localizedMap_bijective

@[simp]
theorem localizedMapEquiv_apply (f : BoundedAlgHom K R S) :
    localizedMapEquiv.{u, v} R S f = localizationFunctor.map (map.{u, v} f) :=
  rfl

/-- Composition of localized spectrum maps retains the entire bounded
composite in the opposite direction. -/
theorem localizedMapEquiv_comp {T : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum T)] (f : BoundedAlgHom K R S) (g : BoundedAlgHom K S T) :
    localizedMapEquiv.{u, v} R T (g.comp f) =
      localizedMapEquiv.{u, v} S T g ≫ localizedMapEquiv.{u, v} R S f := by
  simp only [localizedMapEquiv_apply, map_comp, Functor.map_comp]

end Langlands.Analytic.SmallAffinoidSpectrum
