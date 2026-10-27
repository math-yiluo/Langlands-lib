import Langlands.Geometry.Analytic.StrictTestDomain.SpectralContinuousAction
import Langlands.Geometry.Analytic.StrictTestDomain.SpectralGlobalAction
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Invariant rational spectra over the global continuous spectrum -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : RationalSpectralAction G P)

/-- Restrict the actual continuous global spectrum action to an open subgroup. -/
def restrictedGlobalSpectrum (U : OpenSubgroup G) : ContAction TopCat.{u} U :=
  (ContAction.res TopCat.{u}
    { toMonoidHom := U.toSubgroup.subtype
      continuous_toFun := continuous_subtype_val }).obj ρ.globalSpectrum

@[simp]
theorem restrictedGlobalSpectrum_apply (U : OpenSubgroup G) (g : U)
    (x : BanachSpectrum P) (a : P) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom ((ρ.restrictedGlobalSpectrum U).obj.ρ g) x) a =
        x ((ρ.toMonoidHom (g : G)).inv.toAlgHom a) :=
  rfl

/-- The actual structural map of an invariant rational quotient is a morphism
of continuous actions to the restricted global spectrum. -/
def invariantSpectrumToBase (U : OpenSubgroup G)
    (d : ρ.InvariantRationalDomain U) :
    ρ.invariantSpectrum U d ⟶ ρ.restrictedGlobalSpectrum U :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom (BanachSpectrum.comapContinuous d.obj.baseMap.toBoundedRingHom)
      comm := fun g => by
        apply TopCat.ext
        intro x
        exact ρ.spectrumMap_smul d.obj (ρ.invariantStabilizerInclusion U d g) x }

@[simp]
theorem invariantSpectrumToBase_apply (U : OpenSubgroup G)
    (d : ρ.InvariantRationalDomain U) (x : BanachSpectrum d.obj.algebra) :
    (ρ.invariantSpectrumToBase U d).hom.hom x = d.obj.spectrumMap x :=
  rfl

@[simp]
theorem invariantSpectrumToBase_apply_eval (U : OpenSubgroup G)
    (d : ρ.InvariantRationalDomain U) (x : BanachSpectrum d.obj.algebra) (a : P) :
    BanachSpectrum.toMulRingSeminorm
      ((ρ.invariantSpectrumToBase U d).hom.hom x) a = x (d.obj.baseMap a) :=
  rfl

/-- Each rational inclusion is a triangle over the actual base spectrum. -/
theorem invariantSpectrumToBase_naturality (U : OpenSubgroup G)
    {d e : ρ.InvariantRationalDomain U} (h : d ⟶ e) :
    (ρ.invariantSpectrumFunctor U).map h ≫ ρ.invariantSpectrumToBase U e =
      ρ.invariantSpectrumToBase U d := by
  apply ObjectProperty.hom_ext _
  apply Action.Hom.ext
  apply TopCat.ext
  intro x
  exact h.hom.spectrumMap_restriction x

/-- The equivariant structural maps form a natural transformation to the
constant global spectrum diagram. -/
def invariantSpectrumToBaseNatTrans (U : OpenSubgroup G) :
    ρ.invariantSpectrumFunctor U ⟶
      (Functor.const (ρ.InvariantRationalDomain U)).obj (ρ.restrictedGlobalSpectrum U) where
  app d := ρ.invariantSpectrumToBase U d
  naturality d e h := by
    change (ρ.invariantSpectrumFunctor U).map h ≫ ρ.invariantSpectrumToBase U e =
      ρ.invariantSpectrumToBase U d ≫ 𝟙 (ρ.restrictedGlobalSpectrum U)
    rw [Category.comp_id]
    exact ρ.invariantSpectrumToBase_naturality U h

/-- The actual invariant rational spectrum diagram, retaining its continuous
equivariant structural maps to the global spectrum. -/
def invariantSpectrumOverFunctor (U : OpenSubgroup G) :
    ρ.InvariantRationalDomain U ⥤ Over (ρ.restrictedGlobalSpectrum U) :=
  Over.lift (ρ.invariantSpectrumFunctor U) (ρ.invariantSpectrumToBaseNatTrans U)

@[simp]
theorem invariantSpectrumOverFunctor_obj_hom (U : OpenSubgroup G)
    (d : ρ.InvariantRationalDomain U) :
    ((ρ.invariantSpectrumOverFunctor U).obj d).hom = ρ.invariantSpectrumToBase U d :=
  rfl

@[simp]
theorem invariantSpectrumOverFunctor_map_left (U : OpenSubgroup G)
    {d e : ρ.InvariantRationalDomain U} (h : d ⟶ e) :
    ((ρ.invariantSpectrumOverFunctor U).map h).left =
      (ρ.invariantSpectrumFunctor U).map h :=
  rfl

/-- Forgetting the structural maps recovers the published continuous-action
diagram exactly. -/
@[simp]
theorem invariantSpectrumOverFunctor_forget (U : OpenSubgroup G) :
    ρ.invariantSpectrumOverFunctor U ⋙ Over.forget (ρ.restrictedGlobalSpectrum U) =
      ρ.invariantSpectrumFunctor U :=
  rfl

/-- Forgetting structural maps and actions recovers the original actual
rational quotient spectrum diagram. -/
@[simp]
theorem invariantSpectrumOverFunctor_forget_topological (U : OpenSubgroup G) :
    ρ.invariantSpectrumOverFunctor U ⋙ Over.forget (ρ.restrictedGlobalSpectrum U) ⋙
        forget₂ _ TopCat.{u} =
      (ρ.invariantRationalProperty U).ι ⋙ RationalData.toTopologicalSpace K P :=
  rfl

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
