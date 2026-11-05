import Langlands.AlgebraicGeometry.Modules.ClosedImmersionCohomologyMap
import Langlands.AlgebraicGeometry.Modules.BaseChangeResolution

/-! # Closed-immersion cohomology maps through compatible resolutions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {Y Z : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (g : Y ⟶ Spec R) (g' : Z ⟶ Spec S)
  (h : Z ⟶ Y) [IsClosedImmersion h]
  (w : h ≫ g = g' ≫ Spec.map φ)
  {M : Y.Modules} {N : Z.Modules}
  {K : CochainComplex Y.Modules ℕ} {L : CochainComplex Z.Modules ℕ}
  (ε : (CochainComplex.single₀ Y.Modules).obj M ⟶ K) [QuasiIso ε]
  (η : (CochainComplex.single₀ Z.Modules).obj N ⟶ L) [QuasiIso η]
  (a : M ⟶ (Scheme.Modules.pushforward h).obj N)
  (t : K ⟶ ((Scheme.Modules.pushforward h).mapHomologicalComplex _).obj L)
  (ht : ε ≫ t = (CochainComplex.single₀ Y.Modules).map a ≫
    mapResolutionAugmentation (Scheme.Modules.pushforward h) η)

/-- The cohomology map computed from a cochain map on sections and a target
right-resolution comparison. -/
def closedImmersionResolutionCohomologyMap (n : ℕ) :
    (homologyFunctor (ModuleCat R) _ n).obj
        (((relativeGlobalSections g).mapHomologicalComplex _).obj K) ⟶
      (ModuleCat.restrictScalars φ.hom).obj ((relativeCohomology g' n).obj N) :=
  (homologyFunctor (ModuleCat R) _ n).map
      (resolutionSectionsBaseChangeMap φ g g' h w t) ≫
    (DerivedComparison.mapHomologyIso (ModuleCat.restrictScalars φ.hom)
      (((relativeGlobalSections g').mapHomologicalComplex _).obj L) n).hom ≫
    (ModuleCat.restrictScalars φ.hom).map
      (resolutionComparison (relativeGlobalSections g') η n)

include ht in
/-- An actual map into a closed-immersion pushforward is computed on any
compatible right resolutions. -/
@[reassoc]
theorem resolutionComparison_closedImmersionCohomologyMap (n : ℕ) :
    resolutionComparison (relativeGlobalSections g) ε n ≫
        closedImmersionCohomologyMap φ g g' h w a n =
      closedImmersionResolutionCohomologyMap φ g g' h w η t n := by
  have := ClosedImmersionHigherDirectImageVanishing.pushforward_preservesEpimorphisms h
  have : (Scheme.Modules.pushforward h).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have hp := resolutionComparison_inv_pushforwardComparison h g ε η a t ht
    (fun q => closedImmersionHigherDirectImageVanishing Z Y h inferInstance N q)
    (fun J hJ q => (pushforwardInjectiveAcyclic Z Y h J hJ q).2 R g) n
  change resolutionComparison (relativeGlobalSections g) ε n ≫
      (relativeCohomology g n).map a ≫
      (pushforwardCohomologyIso h g N
        (fun q => closedImmersionHigherDirectImageVanishing Z Y h inferInstance N q) n).inv = _
    at hp
  have hc := congrArg (fun z => z ≫
    (relativeCohomologyBaseRingIso φ (h ≫ g) g' w n).hom.app N) hp
  have hb := resolutionComparison_baseRingIso φ (h ≫ g) g' w η n
  dsimp only [relativeCohomology] at hc hb
  simp only [Category.assoc] at hc
  rw [hb] at hc
  simpa only [closedImmersionCohomologyMap, closedImmersionResolutionCohomologyMap,
    resolutionSectionsBaseChangeMap, Functor.map_comp,
    relativeCohomology, Functor.comp_obj, Category.assoc] using hc

end Langlands.AlgebraicGeometry.Modules.DerivedSections
