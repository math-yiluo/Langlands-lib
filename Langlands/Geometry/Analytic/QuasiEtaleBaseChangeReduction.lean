import Langlands.Geometry.Analytic.QuasiEtaleLocalDomainFactorizationsStatement
import Langlands.Geometry.Analytic.QuasiEtalePullbackLocality
import Langlands.Geometry.Analytic.QuasiEtaleStabilityStatement
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof
import Langlands.Geometry.Analytic.EtaleBaseChangeReduction

/-! # Quasi-étale base change from local domain–étale factorizations -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Étale arrows of the localized category are stable under base change along every pullback
square: compare the given square with the pullback supplied by
`localizedEtalePullbackBaseChange`. -/
theorem localizedEtaleBaseChange : LocalizedEtaleBaseChangeStatement.{u, v} K where
  of_isPullback {_ _ _ _} {f} {g} {_} {_} sq hg := by
    obtain ⟨_, _, _, hP, hq⟩ := localizedEtalePullbackBaseChange (K := K) g f hg
    exact etale_snd_of_isPullback hP sq hq

/-- Base change of a quasi-étale arrow whose source has local domain–étale factorizations:
the factorizations pull back along the square and give the quasi-étale predicate. -/
theorem quasiEtale_of_isPullback_of_hasLocalDomainEtaleFactorizations
    {X Y Y' S : LocalizedCategory.{u, v, v} (K := K)}
    {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : HasLocalDomainEtaleFactorizations g) :
    quasiEtale g' := by
  have : (etale (K := K) :
      MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).IsStableUnderBaseChange :=
    localizedEtaleBaseChange
  exact (hg.of_isPullback sq).quasiEtale

/-- Base change of a quasi-étale arrow with Hausdorff source is quasi-étale. -/
theorem quasiEtale_of_isPullback_of_t2Space
    {X Y Y' S : LocalizedCategory.{u, v, v} (K := K)}
    {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    [T2Space (localizedSpaceFunctor.obj Y)]
    (sq : IsPullback f' g' g f) (hg : quasiEtale g) : quasiEtale g' :=
  quasiEtale_of_isPullback_of_hasLocalDomainEtaleFactorizations sq
    (hasLocalDomainEtaleFactorizations_of_quasiEtale hg)

set_option linter.defProp false in
/-- Reduction of quasi-étale base change to local domain–étale factorizations for quasi-étale
arrows with arbitrary source. It is declared with `def` (its type is a proposition) so that it
can be recorded as a supporting definition artifact. -/
def quasiEtaleBaseChange_of_localDomainFactorizations
    (h : QuasiEtaleLocalDomainFactorizationsStatement.{u, v} K) :
    QuasiEtaleBaseChangeStatement.{u, v} K where
  of_isPullback sq hg := quasiEtale_of_isPullback_of_hasLocalDomainEtaleFactorizations sq (h _ hg)

end Langlands.Analytic.SaturatedAtlasPresentation
