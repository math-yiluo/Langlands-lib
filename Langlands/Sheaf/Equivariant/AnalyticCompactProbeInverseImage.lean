import Langlands.Sheaf.Equivariant.AnalyticCompactProbeQuasiEtale
import Langlands.Geometry.Analytic.EquivariantCompactProbeTopology
import Langlands.Sheaf.Equivariant.AnalyticInverseImage
import Langlands.Sheaf.ImagePullbackContinuity
import Mathlib.CategoryTheory.Sites.InducedTopology

/-! # The compact-probe quasi-étale inverse-image adjunction -/

noncomputable section

universe u v z uR

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Sheaf (HasImagePullbacks)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G] (X : GSpace.{u, v, v} K G)
  (R : Type (max u (v + 1) z uR)) [CommRing R]

local notation "J" => twistedCompactProbeQuasiEtaleTopology X.obj.ρAut
local notation "Jg" => equivariantCompactProbeQuasiEtaleTopology X

/-- Continuity of forgetting the action from a compact-probe equivariant test object
follows from the image pullback criterion. -/
theorem compactProbeToQuasiEtaleSite_isContinuous
    (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)) :
    (EquivariantQuasiEtaleSite.toQuasiEtaleSite X).IsContinuous Jg
      (compactProbeQuasiEtaleTopology X.obj.V) := by
  let F := EquivariantQuasiEtaleSite.toQuasiEtaleSite X
  let J₀ := compactProbeQuasiEtaleTopology X.obj.V
  have hJ : J₀.toPrecoverage.toGrothendieck = J₀ := by
    refine le_antisymm J₀.toGrothendieck_toPrecoverage_le ?_
    intro U S hS
    rw [← Sieve.generate_sieve S]
    exact Precoverage.generate_mem_toGrothendieck ((J₀.arrows_mem_toPrecoverage_iff S).2 hS)
  change F.IsContinuous (J₀.toPrecoverage.comap F).toGrothendieck J₀
  simpa only [hJ] using
    hX.isContinuous (J₀.toPrecoverage.comap F) J₀.toPrecoverage (fun _ _ h => h)

/-- The functor from equivariant test objects to the twisted category is continuous
under the geometric image-pullback input. -/
theorem compactProbeQuasiEtaleToTwisted_isContinuous
    (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)) :
    (quasiEtaleToTwisted X).IsContinuous Jg J :=
  let : (EquivariantQuasiEtaleSite.toQuasiEtaleSite X).IsContinuous Jg
      (compactProbeQuasiEtaleTopology X.obj.V) := compactProbeToQuasiEtaleSite_isContinuous X hX
  Functor.isContinuous_comp _ _ _ (compactProbeQuasiEtaleTopology X.obj.V) _

/-- Sheafification on the twisted compact-probe site at the indicated coefficient universe. -/
private theorem twistedSiteHasSheafify : HasSheafify J (ModuleCat.{max u (v + 1) z uR} R) :=
  let : Small.{max u (v + 1) z uR} G := small_lift.{z, max u (v + 1) uR, z} G
  let := twistedQuasiEtale_essentiallySmall_points.{u, v, max z uR} X.obj.V X.obj.ρAut
  hasSheafifyEssentiallySmallSite _ _

variable (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X))

/-- The sheaf of invariant sections `V(G) ↦ F(V)^G` on the equivariant
compact-probe site. -/
def compactProbeQuasiEtaleInvariantSheaf : Sheaf J (ModuleCat.{max u (v + 1) z uR} R) ⥤ Sheaf Jg (ModuleCat.{max u (v + 1) z uR} R) :=
  letI := compactProbeQuasiEtaleToTwisted_isContinuous X hX
  (quasiEtaleNaturalAction X).sheafInvariantSheafFunctor R J Jg

/-- The underlying presheaf is the original invariant-section presheaf. -/
def compactProbeQuasiEtaleInvariantSheafCompIso :
    compactProbeQuasiEtaleInvariantSheaf.{u, v, z, uR} X R hX ⋙ sheafToPresheaf Jg (ModuleCat.{max u (v + 1) z uR} R) ≅
      (quasiEtaleNaturalAction X).sheafInvariantFunctor R J :=
  letI := compactProbeQuasiEtaleToTwisted_isContinuous X hX
  (quasiEtaleNaturalAction X).sheafInvariantSheafFunctorCompIso R J Jg

/-- The inverse image is sheafification of the actual left Kan extension of the
inflated presheaf. -/
def compactProbeQuasiEtaleInverseImage : Sheaf Jg (ModuleCat.{max u (v + 1) z uR} R) ⥤ Sheaf J (ModuleCat.{max u (v + 1) z uR} R) :=
  letI := quasiEtaleInflation_hasLeftKanExtension.{u, v, uR, z} X R
  letI := twistedSiteHasSheafify.{u, v, z, uR} X R
  (quasiEtaleNaturalAction X).sheafInverseImageFunctor R J Jg

/-- The compact-probe inverse image is left adjoint to invariant sections. -/
def compactProbeQuasiEtaleInverseImageAdjunction :
    compactProbeQuasiEtaleInverseImage.{u, v, z, uR} X R ⊣
      compactProbeQuasiEtaleInvariantSheaf.{u, v, z, uR} X R hX :=
  letI := quasiEtaleInflation_hasLeftKanExtension.{u, v, uR, z} X R
  letI := twistedSiteHasSheafify.{u, v, z, uR} X R
  letI := compactProbeQuasiEtaleToTwisted_isContinuous X hX
  (quasiEtaleNaturalAction X).sheafInverseImageAdjunction R J Jg

end Langlands.Sheaf.Equivariant.Analytic
