import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Langlands.Geometry.Analytic.SmallAffinoidSpectrum
import Langlands.Geometry.Analytic.SaturatedStrongLocalization

/-! # Descent along finite étale affinoid covers into good targets -/

universe u v

open CategoryTheory Set
open scoped Topology

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- A morphism from the source of a finite étale, spectrum-surjective affinoid map descends
if it satisfies the kernel-pair condition and its target has a chart neighbourhood at
every point. This is the finite étale affinoid case of the existence conclusion for a
good target in Berkovich 1993, Proposition 4.1.3. -/
def FiniteEtaleAffinoidHomDescentGoodTargetStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A B : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum A)]
    [Small.{v} (BanachSpectrum B)] (f : BoundedAlgHom K A B),
    f.IsFiniteBanach → f.AlgebraicallyFiniteEtale →
    Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom) →
    ∀ (T : SaturatedAtlasPresentation.{u, v, v} K),
      (∀ t : T.presentation.space,
        ∃ e : T.presentation.atlas.Index, range (T.presentation.atlas.chart e) ∈ 𝓝 t) →
      ∀ (g : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B) ⟶
          localizationFunctor.obj T),
        (∀ (Z : LocalizedCategory.{u, v, v} (K := K))
            (a b : Z ⟶ localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B)),
            a ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) =
                b ≫ localizationFunctor.map (SmallAffinoidSpectrum.map f) →
              a ≫ g = b ≫ g) →
        ∃ h : localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} A) ⟶
            localizationFunctor.obj T,
          localizationFunctor.map (SmallAffinoidSpectrum.map f) ≫ h = g

end Langlands.Analytic.SaturatedAtlasPresentation
