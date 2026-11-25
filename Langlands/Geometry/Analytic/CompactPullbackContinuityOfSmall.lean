import Langlands.Geometry.Analytic.CompactPullbackActionContinuity
import Langlands.Geometry.Analytic.CompactPullbackActionContinuitySmall
import Langlands.Geometry.Analytic.AffinoidPatchGoodCharts
import Langlands.Geometry.Analytic.LocallyGoodChartContinuity
import Langlands.Geometry.Analytic.PairChartConvergence
import Langlands.Geometry.Analytic.PairChartCover

/-! # Continuity on compact analytic pullbacks under pair-chart smallness -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type z} [Group G] [TopologicalSpace G]

variable (K) in
/-- The Berkovich spectrum of every presented affinoid algebra over `K` is
small in the space universe `v`. -/
def AffinoidSpectraSmall : Prop :=
  ∀ R : PresentedAffinoidAlgebra K, Small.{v} (BanachSpectrum R)

omit [CompleteSpace K] in
/-- The smallness hypothesis holds whenever the field universe is at most the
space universe. -/
theorem affinoidSpectraSmall_of_univLE [UnivLE.{u, v}] : AffinoidSpectraSmall.{u, v} K :=
  fun _ => inferInstance

/-- If all spectra of presented affinoid algebras are small in the space
universe, an action on a pullback whose projections are equivariant for
continuous actions on the factors is locally covered by good charts. -/
theorem isLocallyGood_of_pullback_of_small
    (hS : AffinoidSpectraSmall.{u, v} K)
    {B U V P : LocalizedCategory.{u, v, v} (K := K)}
    {f : U ⟶ B} {g : V ⟶ B} {p : P ⟶ U} {q : P ⟶ V} (hP : IsPullback p q f g)
    {σ : G →* Aut P} {σU : G →* Aut U} {σV : G →* Aut V}
    (hU : IsContinuousAction σU) (hV : IsContinuousAction σV)
    (hp : ∀ h, (σ h).asIso.hom ≫ p = p ≫ (σU h).asIso.hom)
    (hq : ∀ h, (σ h).asIso.hom ≫ q = q ≫ (σV h).asIso.hom) :
    IsLocallyGood σ := fun y =>
  isLocallyChartCovered_of_pairCharts hP.w (IsGoodChart σ) (fun c W hW => by
    have := hS c.algebra
    exact isGoodChart_of_affinoidPatch (c.eventually_preimage_patch hU hV hp hq)
      (c.spectralConvergesOn_patchPullback hP hU hV hp hq) W hW) y

/-- Continuity on a compact analytic pullback, assuming smallness of the
spectra of presented affinoid algebras. -/
theorem compactPullbackActionContinuity_of_small :
    CompactPullbackActionContinuitySmallStatement.{u, v, z} (K := K) (G := G) := by
  intro hS B U V P f g p q _ _ _ hPc hP σ σU σV hU hV hp hq
  have := hPc.2
  exact isContinuousAction_of_locallyGood
    (isLocallyGood_of_pullback_of_small hS hP hU hV hp hq)

/-- When the field universe is at most the space universe, the pullback
continuity statement holds as stated. -/
theorem compactPullbackActionContinuityStatement_of_univLE [UnivLE.{u, v}] :
    CompactPullbackActionContinuityStatement.{u, v, z} (K := K) (G := G) :=
  compactPullbackActionContinuity_of_small affinoidSpectraSmall_of_univLE

/-- When the field and the spaces live in the same universe, the pullback
continuity statement holds as stated. -/
theorem compactPullbackActionContinuityStatement_of_univ_eq :
    CompactPullbackActionContinuityStatement.{u, u, z} (K := K) (G := G) :=
  compactPullbackActionContinuity_of_small (affinoidSpectraSmall_of_univLE.{u, u} (K := K))

end Langlands.Analytic.SaturatedAtlasPresentation
