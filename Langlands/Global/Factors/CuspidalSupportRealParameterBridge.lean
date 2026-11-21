import Langlands.Automorphic.ArchimedeanParameterReduction
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Automorphic.PlaceComponentExistence
import Langlands.Automorphic.CuspidalWhittaker.PlaceWhittaker
import Langlands.Representation.Archimedean.RealLanglandsQuotientReduction
import Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientProof
import Langlands.Representation.Archimedean.RealLanglandsFromPrincipalSeriesProof
import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter
import Langlands.Representation.Archimedean.RealWhittakerMaximallyFaithfulProof
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientInjectiveProof

/-! # Real cuspidal parameters for the every-place support proof -/

universe u

set_option autoImplicit false

namespace Langlands.Global

open Langlands.Automorphic

private theorem realGenericParameter : Archimedean.RealGenericStandardParameterStatement.{u} :=
  Archimedean.realGenericStandardParameterReduction
    (Archimedean.realLanglandsQuotientReduction Archimedean.realPrincipalSeriesQuotient
      Archimedean.realLanglandsFromPrincipalSeries)
    (Archimedean.realGenericLargeReduction
      Archimedean.InfinitesimalCharacter.realGKModuleInfinitesimalCharacter
      Archimedean.Kostant.realWhittakerMaximallyFaithful
      Archimedean.realLargeLanglandsQuotientInjective)

theorem realCuspidalParameters
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) :
    ∃ ds, T.realization.HasRealPlaceParameter v ds := by
  obtain ⟨V, _, _, ρ, π, ι, hι, hρ, hπ, hgk, hirr, hadm, hgen⟩ :=
    (cuspidalArchimedeanGenericComponentBridge cuspidalArchimedeanIrreducibleAdmissibleComponent
      cuspidalArchimedeanWhittakerFunctional F r T).1 v
  obtain ⟨ds, hds⟩ := realGenericParameter (r + 1) V ρ π hgk hirr hadm hgen
  exact ⟨ds, OperatorRealization.hasRealPlaceParameter_of_component hι hρ hπ hds⟩

end Langlands.Global
