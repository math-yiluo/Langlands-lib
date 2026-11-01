import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainContinuousLocus
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainInvariantSpectrumOverBase

/-! # Continuous spectrum and locus quotient diagrams over the actual base -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)

/-- Restrict the proved jointly continuous global spectrum action without
changing the underlying space or any operator. -/
def restrictedGlobalSpectrum (H : OpenSubgroup G) : ContAction TopCat.{u} H :=
  (ContAction.res TopCat.{u}
    { toMonoidHom := H.toSubgroup.subtype
      continuous_toFun := continuous_subtype_val }).obj ρ.globalSpectrum

@[simp]
theorem restrictedGlobalSpectrum_toAction (H : OpenSubgroup G) :
    (ρ.restrictedGlobalSpectrum H).obj = ρ.restrictedGlobalSpectrumAction H := rfl

@[simp]
theorem restrictedGlobalSpectrum_apply (H : OpenSubgroup G) (g : H)
    (x : BanachSpectrum P) (a : P) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom ((ρ.restrictedGlobalSpectrum H).obj.ρ g) x) a =
        x ((ρ.toMonoidHom (g : G)).inv.toAlgHom a) := rfl

/-- Lift the existing actual bounded structural pullback to continuous actions. -/
def invariantSpectrumToBase (H : OpenSubgroup G) (d : ρ.InvariantDomain H) :
    (ρ.invariantSpectrumFunctor H).obj d ⟶ ρ.restrictedGlobalSpectrum H :=
  ObjectProperty.homMk (ρ.invariantSpectrumActionToBase H d)

@[simp]
theorem invariantSpectrumToBase_apply (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) (x : BanachSpectrum d.obj.algebra) :
    (ρ.invariantSpectrumToBase H d).hom.hom x = d.obj.spectrumMap x := rfl

@[simp]
theorem invariantSpectrumToBase_apply_eval (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) (x : BanachSpectrum d.obj.algebra) (a : P) :
    BanachSpectrum.toMulRingSeminorm
      ((ρ.invariantSpectrumToBase H d).hom.hom x) a = x (d.obj.baseMap a) := rfl

theorem invariantSpectrumToBase_naturality (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e) :
    (ρ.invariantSpectrumFunctor H).map f ≫ ρ.invariantSpectrumToBase H e =
      ρ.invariantSpectrumToBase H d := by
  apply ObjectProperty.hom_ext _
  exact ρ.invariantSpectrumActionToBase_naturality H f

/-- The actual inclusion of the represented locus in the original spectrum,
with its continuous equivariant structure. -/
def invariantLocusToBase (H : OpenSubgroup G) (d : ρ.InvariantDomain H) :
    (ρ.invariantLocusFunctor H).obj d ⟶ ρ.restrictedGlobalSpectrum H :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom
        { toFun := fun x => (x : BanachSpectrum P)
          continuous_toFun := continuous_subtype_val }
      comm := fun _ => by
        apply TopCat.ext
        intro x
        rfl }

@[simp]
theorem invariantLocusToBase_apply (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) (x : d.obj.locus) :
    (ρ.invariantLocusToBase H d).hom.hom x = (x : BanachSpectrum P) := rfl

theorem invariantLocusToBase_naturality (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e) :
    (ρ.invariantLocusFunctor H).map f ≫ ρ.invariantLocusToBase H e =
      ρ.invariantLocusToBase H d := by
  apply ObjectProperty.hom_ext _
  apply Action.Hom.ext
  apply TopCat.ext
  intro x
  rfl

/-- The quotient factors the original structural spectrum pullback through
the actual locus inclusion, as an equality of continuous action morphisms. -/
theorem invariantSpectrumToLocusContinuous_over_base (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    ρ.invariantSpectrumToLocusContinuous H d ≫ ρ.invariantLocusToBase H d =
      ρ.invariantSpectrumToBase H d := by
  apply ObjectProperty.hom_ext _
  apply Action.Hom.ext
  apply TopCat.ext
  intro x
  rfl

def invariantSpectrumToBaseNatTrans (H : OpenSubgroup G) :
    ρ.invariantSpectrumFunctor H ⟶
      (Functor.const (ρ.InvariantDomain H)).obj (ρ.restrictedGlobalSpectrum H) where
  app d := ρ.invariantSpectrumToBase H d
  naturality _ _ f := by
    change (ρ.invariantSpectrumFunctor H).map f ≫ ρ.invariantSpectrumToBase H _ =
      ρ.invariantSpectrumToBase H _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact ρ.invariantSpectrumToBase_naturality H f

def invariantLocusToBaseNatTrans (H : OpenSubgroup G) :
    ρ.invariantLocusFunctor H ⟶
      (Functor.const (ρ.InvariantDomain H)).obj (ρ.restrictedGlobalSpectrum H) where
  app d := ρ.invariantLocusToBase H d
  naturality _ _ f := by
    change (ρ.invariantLocusFunctor H).map f ≫ ρ.invariantLocusToBase H _ =
      ρ.invariantLocusToBase H _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact ρ.invariantLocusToBase_naturality H f

/-- The full invariant spectrum diagram over the original continuous base action. -/
def invariantSpectrumOverFunctor (H : OpenSubgroup G) :
    ρ.InvariantDomain H ⥤ Over (ρ.restrictedGlobalSpectrum H) :=
  Over.lift (ρ.invariantSpectrumFunctor H) (ρ.invariantSpectrumToBaseNatTrans H)

/-- The full invariant locus diagram over that same continuous base action. -/
def invariantLocusOverFunctor (H : OpenSubgroup G) :
    ρ.InvariantDomain H ⥤ Over (ρ.restrictedGlobalSpectrum H) :=
  Over.lift (ρ.invariantLocusFunctor H) (ρ.invariantLocusToBaseNatTrans H)

@[simp]
theorem invariantSpectrumOverFunctor_obj_hom (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    ((ρ.invariantSpectrumOverFunctor H).obj d).hom =
      ρ.invariantSpectrumToBase H d := rfl

@[simp]
theorem invariantLocusOverFunctor_obj_hom (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    ((ρ.invariantLocusOverFunctor H).obj d).hom = ρ.invariantLocusToBase H d := rfl

@[simp]
theorem invariantSpectrumOverFunctor_map_left (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e) :
    ((ρ.invariantSpectrumOverFunctor H).map f).left =
      (ρ.invariantSpectrumFunctor H).map f := rfl

@[simp]
theorem invariantLocusOverFunctor_map_left (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e) :
    ((ρ.invariantLocusOverFunctor H).map f).left =
      (ρ.invariantLocusFunctor H).map f := rfl

/-- The actual structural quotients assemble over the unchanged original base. -/
def invariantSpectrumToLocusOverNatTrans (H : OpenSubgroup G) :
    ρ.invariantSpectrumOverFunctor H ⟶ ρ.invariantLocusOverFunctor H where
  app d := Over.homMk (ρ.invariantSpectrumToLocusContinuous H d)
    (ρ.invariantSpectrumToLocusContinuous_over_base H d)
  naturality _ _ f := by
    apply Over.OverMorphism.ext
    exact ρ.invariantSpectrumToLocusContinuous_naturality H f

@[simp]
theorem invariantSpectrumToLocusOverNatTrans_app_left (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    ((ρ.invariantSpectrumToLocusOverNatTrans H).app d).left =
      ρ.invariantSpectrumToLocusContinuous H d := rfl

@[simp]
theorem invariantSpectrumOverFunctor_forget (H : OpenSubgroup G) :
    ρ.invariantSpectrumOverFunctor H ⋙ Over.forget (ρ.restrictedGlobalSpectrum H) =
      ρ.invariantSpectrumFunctor H := rfl

@[simp]
theorem invariantLocusOverFunctor_forget (H : OpenSubgroup G) :
    ρ.invariantLocusOverFunctor H ⋙ Over.forget (ρ.restrictedGlobalSpectrum H) =
      ρ.invariantLocusFunctor H := rfl

@[simp]
theorem invariantSpectrumOverFunctor_toAction (H : OpenSubgroup G) :
    ρ.invariantSpectrumOverFunctor H ⋙ Over.post (Action.isContinuous TopCat.{u} H).ι =
      ρ.invariantSpectrumActionOverFunctor H := rfl

@[simp]
theorem invariantSpectrumOverFunctor_forget_topological (H : OpenSubgroup G) :
    ρ.invariantSpectrumOverFunctor H ⋙ Over.forget (ρ.restrictedGlobalSpectrum H) ⋙
        forget₂ _ TopCat.{u} =
      (ρ.invariantDomainProperty H).ι ⋙ Domain.toTopologicalSpace K P := rfl

@[simp]
theorem invariantLocusOverFunctor_forget_topological (H : OpenSubgroup G) :
    ρ.invariantLocusOverFunctor H ⋙ Over.forget (ρ.restrictedGlobalSpectrum H) ⋙
        forget₂ _ TopCat.{u} =
      (ρ.invariantDomainProperty H).ι ⋙ Domain.locusFunctor K P := rfl

@[simp]
theorem invariantSpectrumToLocusOverNatTrans_forget (H : OpenSubgroup G) :
    Functor.whiskerRight (ρ.invariantSpectrumToLocusOverNatTrans H)
        (Over.forget (ρ.restrictedGlobalSpectrum H)) =
      ρ.invariantSpectrumToLocusContinuousNatTrans H := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
