import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralLocalContinuityProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainWholeAction

/-! # The global spectrum action from full represented-domain tests
-/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)

/-- Joint continuity on the whole spectrum follows from the full-domain
local theorem and equality of the actual whole-domain section maps. -/
theorem continuous_globalSpectrumAction :
    Continuous (fun p : G × BanachSpectrum P => ρ.toMonoidHom p.1 • p.2) := by
  have hl :=
    (domainSpectralLocalContinuity K P G ρ
      (Domain.whole K P)).2.2
  have hi : Continuous (fun p : G × BanachSpectrum P =>
      (ρ.wholeStabilizerHom p.1, (p.2 : BanachSpectrum (Domain.whole K P).algebra))) :=
    (ρ.wholeStabilizerHom.continuous.comp continuous_fst).prodMk continuous_snd
  have hc := hl.comp hi
  change Continuous (fun p : G × BanachSpectrum P =>
    (show Aut P from ρ.sectionAction (Domain.whole K P)
      (ρ.wholeStabilizerHom p.1)) • p.2) at hc
  simpa only [ρ.sectionAction_whole] using hc

/-- The actual global continuous action with derived joint continuity. -/
def globalSpectrum : ContAction TopCat.{u} G :=
  ⟨ρ.globalSpectrumAction, (Action.isContinuous_def _).mpr
    (ρ.continuous_globalSpectrumAction)⟩

@[simp]
theorem globalSpectrum_apply (g : G) (x : BanachSpectrum P) (a : P) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom ((ρ.globalSpectrum).obj.ρ g) x) a =
        x ((ρ.toMonoidHom g).inv.toAlgHom a) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
