import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainInvariantActions
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainWholeAction
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Invariant represented-domain spectrum actions over the base -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)

/-- Restrict the original inverse-pullback spectrum action to the common
open subgroup, retaining its actual operators. -/
def restrictedGlobalSpectrumAction (H : OpenSubgroup G) : Action TopCat.{u} H :=
  (Action.res TopCat.{u} H.toSubgroup.subtype).obj ρ.globalSpectrumAction

@[simp]
theorem restrictedGlobalSpectrumAction_apply (H : OpenSubgroup G) (g : H)
    (x : BanachSpectrum P) (a : P) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom ((ρ.restrictedGlobalSpectrumAction H).ρ g) x) a =
        x ((ρ.toMonoidHom (g : G)).inv.toAlgHom a) :=
  rfl

/-- The actual structural pullback intertwines the constructed local and
original global inverse-pullback actions. -/
def invariantSpectrumActionToBase (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    (ρ.invariantSpectrumActionFunctor H).obj d ⟶ ρ.restrictedGlobalSpectrumAction H where
  hom := TopCat.ofHom (BanachSpectrum.comapContinuous d.obj.baseMap.toBoundedRingHom)
  comm g := by
    apply TopCat.ext
    intro x
    exact ρ.spectrumMap_smul d.obj (ρ.invariantStabilizerInclusion H d g) x

@[simp]
theorem invariantSpectrumActionToBase_apply (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) (x : BanachSpectrum d.obj.algebra) :
    (ρ.invariantSpectrumActionToBase H d).hom x = d.obj.spectrumMap x :=
  rfl

@[simp]
theorem invariantSpectrumActionToBase_apply_eval (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) (x : BanachSpectrum d.obj.algebra) (a : P) :
    BanachSpectrum.toMulRingSeminorm
      ((ρ.invariantSpectrumActionToBase H d).hom x) a = x (d.obj.baseMap a) :=
  rfl

/-- A represented-domain restriction gives a commuting triangle over the
original quotient spectrum. -/
theorem invariantSpectrumActionToBase_naturality (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e) :
    (ρ.invariantSpectrumActionFunctor H).map f ≫ ρ.invariantSpectrumActionToBase H e =
      ρ.invariantSpectrumActionToBase H d := by
  apply Action.Hom.ext
  apply TopCat.ext
  intro x
  exact f.hom.spectrumMap_over_base x

/-- Structural pullbacks form a natural transformation to the constant
restricted global action. -/
def invariantSpectrumActionToBaseNatTrans (H : OpenSubgroup G) :
    ρ.invariantSpectrumActionFunctor H ⟶
      (Functor.const (ρ.InvariantDomain H)).obj (ρ.restrictedGlobalSpectrumAction H) where
  app d := ρ.invariantSpectrumActionToBase H d
  naturality d e f := by
    change (ρ.invariantSpectrumActionFunctor H).map f ≫
        ρ.invariantSpectrumActionToBase H e =
      ρ.invariantSpectrumActionToBase H d ≫ 𝟙 (ρ.restrictedGlobalSpectrumAction H)
    rw [Category.comp_id]
    exact ρ.invariantSpectrumActionToBase_naturality H f

/-- The invariant domain diagram retains its actual equivariant structural
maps as a diagram over the restricted global spectrum action. -/
def invariantSpectrumActionOverFunctor (H : OpenSubgroup G) :
    ρ.InvariantDomain H ⥤ Over (ρ.restrictedGlobalSpectrumAction H) :=
  Over.lift (ρ.invariantSpectrumActionFunctor H) (ρ.invariantSpectrumActionToBaseNatTrans H)

@[simp]
theorem invariantSpectrumActionOverFunctor_obj_hom (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) :
    ((ρ.invariantSpectrumActionOverFunctor H).obj d).hom =
      ρ.invariantSpectrumActionToBase H d :=
  rfl

@[simp]
theorem invariantSpectrumActionOverFunctor_map_left (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e) :
    ((ρ.invariantSpectrumActionOverFunctor H).map f).left =
      (ρ.invariantSpectrumActionFunctor H).map f :=
  rfl

/-- Forgetting the maps to the base recovers the original equivariant diagram. -/
@[simp]
theorem invariantSpectrumActionOverFunctor_forget (H : OpenSubgroup G) :
    ρ.invariantSpectrumActionOverFunctor H ⋙
        Over.forget (ρ.restrictedGlobalSpectrumAction H) =
      ρ.invariantSpectrumActionFunctor H :=
  rfl

/-- Forgetting structural maps and actions retains the exact original
topological realization of the full invariant domain category. -/
@[simp]
theorem invariantSpectrumActionOverFunctor_forget_topological (H : OpenSubgroup G) :
    ρ.invariantSpectrumActionOverFunctor H ⋙
        Over.forget (ρ.restrictedGlobalSpectrumAction H) ⋙ Action.forget TopCat.{u} H =
      (ρ.invariantDomainProperty H).ι ⋙ Domain.toTopologicalSpace K P :=
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
