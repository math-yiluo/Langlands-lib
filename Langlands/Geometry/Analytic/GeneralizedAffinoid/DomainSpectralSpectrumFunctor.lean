import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralGlobalAction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralActionCategory

/-! # Actual spectra and all equivariant bounded maps
-/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainSpectralActionCategory

open CategoryTheory

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- Every actual equivariant bounded map intertwines inverse spectrum pullback. -/
theorem spectrumMap_equivariant {X Y : DomainSpectralActionCategory K G}
    (f : X ⟶ Y) (g : G) (x : BanachSpectrum Y.obj.V) :
    BanachSpectrum.comap (homMap f).toBoundedRingHom ((Y.actionAut g) • x) =
      (X.actionAut g) • BanachSpectrum.comap (homMap f).toBoundedRingHom x := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun b : Y.obj.V => x b) (homMap_apply_action f (g⁻¹) a).symm

/-- The actual spectrum functor on every represented-domain spectral action
and every equivariant bounded algebra arrow, in geometric direction. -/
def spectrumFunctor :
    DomainSpectralSpace K G ⥤ ContAction TopCat.{u} G where
  obj X := X.unop.toDomainSpectralAction.globalSpectrum
  map f := ObjectProperty.homMk
    { hom := TopCat.ofHom (BanachSpectrum.comapContinuous (homMap f.unop).toBoundedRingHom)
      comm := fun g => by
        apply TopCat.ext
        intro x
        exact spectrumMap_equivariant f.unop g x }
  map_id _ := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    exact BanachSpectrum.ext fun _ => rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    exact BanachSpectrum.ext fun _ => rfl

@[simp]
theorem spectrumFunctor_obj_apply (X : DomainSpectralSpace K G)
    (g : G) (x : BanachSpectrum X.unop.obj.V) (a : X.unop.obj.V) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom (((spectrumFunctor).obj X).obj.ρ g) x) a =
        x ((X.unop.actionAut g).inv.toAlgHom a) := rfl

@[simp]
theorem spectrumFunctor_map_apply {X Y : DomainSpectralSpace K G}
    (f : X ⟶ Y) (x : BanachSpectrum X.unop.obj.V) (a : Y.unop.obj.V) :
    BanachSpectrum.toMulRingSeminorm (((spectrumFunctor).map f).hom.hom x) a =
      x ((homMap f.unop).toAlgHom a) := rfl

/-- Forgetting the continuous group action recovers the actual affinoid
spectrum functor, with every original bounded pullback. -/
@[simp]
theorem spectrumFunctor_forget :
    spectrumFunctor (K := K) (G := G) ⋙ forget₂ _ TopCat.{u} =
      (forget (K := K) (G := G)).op ⋙ affinoidSpectrumFunctor K := by
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainSpectralActionCategory
