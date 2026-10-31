import Langlands.Geometry.Analytic.GeneralizedAffinoid.VariableActionFibered
import Langlands.Topology.GroupAction.VariableContinuousActionFibered

/-! # Actual quotient spectra and the operator-group fibrations -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

/-- Actual spectra retain exactly the original topological groups and maps. -/
theorem spectrumFunctor_comp_groupForget :
    (spectrumFunctor : VariableActionSpace.{u, v} K ⥤ _) ⋙
        Langlands.Topology.VariableContinuousAction.groupForget =
      groupForget := rfl

section Restriction

variable (X : VariableActionSpace.{u, v} K)
  {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The comparison identifies the complete spectral restriction arrow with
the canonical restriction arrow of the continuous action. -/
theorem spectrumFunctor_restrictionMap (f : H →ₜ* X.groupType) :
    spectrumFunctor.map (restrictionMap X f) =
      (spectrumRestrictIso X f).hom ≫
        Langlands.Topology.VariableContinuousAction.restrictionMap
          (spectrumFunctor.obj X) f := by
  apply Langlands.Topology.VariableContinuousAction.Hom.ext
  · apply ContinuousMonoidHom.ext
    intro g
    rfl
  · apply TopCat.ext
    intro x
    exact BanachSpectrum.ext fun _ => rfl

/-- The spectrum of a canonical quotient restriction is strongly Cartesian
for the actual continuous-action group functor. -/
instance spectrumFunctor_restrictionMap_isStronglyCartesian
    (H : Langlands.Topology.TopologicalGroup.{v}) (f : H ⟶ groupForget.obj X) :
    Functor.IsStronglyCartesian
      Langlands.Topology.VariableContinuousAction.groupForget f
      (spectrumFunctor.map (restrictionMap X f)) := by
  have hlift : Functor.IsHomLift
      Langlands.Topology.VariableContinuousAction.groupForget (𝟙 H)
      (spectrumRestrictIso X f).hom :=
    IsHomLift.map
      Langlands.Topology.VariableContinuousAction.groupForget
      (spectrumRestrictIso X f).hom
  have hiso : Functor.IsStronglyCartesian
      Langlands.Topology.VariableContinuousAction.groupForget (𝟙 H)
      (spectrumRestrictIso X f).hom :=
    Functor.IsStronglyCartesian.of_iso
      Langlands.Topology.VariableContinuousAction.groupForget (𝟙 H)
      (spectrumRestrictIso X f)
  have hres : Functor.IsStronglyCartesian
      Langlands.Topology.VariableContinuousAction.groupForget f
      (Langlands.Topology.VariableContinuousAction.restrictionMap
        (spectrumFunctor.obj X) f) :=
    Langlands.Topology.VariableContinuousAction.restrictionMap_isStronglyCartesian
      (spectrumFunctor.obj X) H f
  have h : Functor.IsStronglyCartesian
      Langlands.Topology.VariableContinuousAction.groupForget ((𝟙 H) ≫ f)
      ((spectrumRestrictIso X f).hom ≫
        Langlands.Topology.VariableContinuousAction.restrictionMap
          (spectrumFunctor.obj X) f) :=
    @Functor.IsStronglyCartesian.comp _ _ _ _
      Langlands.Topology.VariableContinuousAction.groupForget
      H H (groupForget.obj X) _ _ _ (𝟙 H) f
      (spectrumRestrictIso X f).hom
      (Langlands.Topology.VariableContinuousAction.restrictionMap
        (spectrumFunctor.obj X) f) hiso hres
  have h' : Functor.IsStronglyCartesian
      Langlands.Topology.VariableContinuousAction.groupForget f
      ((spectrumRestrictIso X f).hom ≫
        Langlands.Topology.VariableContinuousAction.restrictionMap
          (spectrumFunctor.obj X) f) := by
    simpa only [Category.id_comp] using h
  exact (spectrumFunctor_restrictionMap X f).symm ▸ h'

variable {X}
  {Z : Langlands.Topology.VariableContinuousAction.{u, v}}

/-- Lift any continuous equivariant arrow to an actual quotient spectrum
through restriction, using the identity-on-seminorms comparison. -/
def spectrumRestrictionLift (f : H →ₜ* X.groupType)
    (h : Z ⟶ spectrumFunctor.obj X) (k : Z.groupType →ₜ* H)
    (hgroup : f.comp k = h.groupHom) :
    Z ⟶ spectrumFunctor.obj (restrict X f) :=
  Langlands.Topology.VariableContinuousAction.restrictionLift
      (X := spectrumFunctor.obj X) f h k hgroup ≫
    (spectrumRestrictIso X f).inv

@[simp]
theorem spectrumRestrictionLift_groupHom (f : H →ₜ* X.groupType)
    (h : Z ⟶ spectrumFunctor.obj X) (k : Z.groupType →ₜ* H)
    (hgroup : f.comp k = h.groupHom) :
    (spectrumRestrictionLift f h k hgroup).groupHom = k := by
  apply ContinuousMonoidHom.ext
  intro g
  rfl

@[simp]
theorem spectrumRestrictionLift_spaceMap (f : H →ₜ* X.groupType)
    (h : Z ⟶ spectrumFunctor.obj X) (k : Z.groupType →ₜ* H)
    (hgroup : f.comp k = h.groupHom) :
    (spectrumRestrictionLift f h k hgroup).spaceMap = h.spaceMap := by
  apply TopCat.ext
  intro z
  rfl

/-- The constructed lift factors the full continuous equivariant arrow. -/
theorem spectrumRestrictionLift_comp_restrictionMap (f : H →ₜ* X.groupType)
    (h : Z ⟶ spectrumFunctor.obj X) (k : Z.groupType →ₜ* H)
    (hgroup : f.comp k = h.groupHom) :
    spectrumRestrictionLift f h k hgroup ≫
      spectrumFunctor.map (restrictionMap X f) = h := by
  apply Langlands.Topology.VariableContinuousAction.Hom.ext
  · change f.comp k = h.groupHom
    exact hgroup
  · apply TopCat.ext
    intro z
    exact BanachSpectrum.ext fun _ => rfl

/-- Prescribing the group map and the full factorization determines the lift. -/
theorem spectrumRestrictionLift_unique (f : H →ₜ* X.groupType)
    (h : Z ⟶ spectrumFunctor.obj X) (k : Z.groupType →ₜ* H)
    (hgroup : f.comp k = h.groupHom)
    (l : Z ⟶ spectrumFunctor.obj (restrict X f)) (lgroup : l.groupHom = k)
    (lfactor : l ≫ spectrumFunctor.map (restrictionMap X f) = h) :
    l = spectrumRestrictionLift f h k hgroup := by
  apply Langlands.Topology.VariableContinuousAction.Hom.ext
  · exact lgroup.trans (spectrumRestrictionLift_groupHom f h k hgroup).symm
  · apply TopCat.ext
    intro z
    change l.spaceMap z = h.spaceMap z
    have hz := congrArg
      (fun q : Z ⟶ spectrumFunctor.obj X => q.spaceMap z) lfactor
    change (spectrumFunctor.map (restrictionMap X f)).spaceMap (l.spaceMap z) =
      h.spaceMap z at hz
    exact (spectrumFunctor_restrictionMap_apply X f (l.spaceMap z)).symm.trans hz

/-- The explicit full unique-lift property allows every continuous source
action, whether or not that source is itself an affinoid spectrum. -/
theorem spectrumRestrictionLift_existsUnique (f : H →ₜ* X.groupType)
    (h : Z ⟶ spectrumFunctor.obj X) (k : Z.groupType →ₜ* H)
    (hgroup : f.comp k = h.groupHom) :
    ∃! l : Z ⟶ spectrumFunctor.obj (restrict X f),
      l.groupHom = k ∧ l ≫ spectrumFunctor.map (restrictionMap X f) = h := by
  refine ⟨spectrumRestrictionLift f h k hgroup,
    ⟨spectrumRestrictionLift_groupHom f h k hgroup,
      spectrumRestrictionLift_comp_restrictionMap f h k hgroup⟩, ?_⟩
  intro l hl
  exact spectrumRestrictionLift_unique f h k hgroup l hl.1 hl.2

variable {Y : VariableActionSpace.{u, v} K}

/-- Spectra carry the constructed quotient lift to the constructed continuous
lift, as an equality of complete arrows. -/
theorem spectrumFunctor_restrictionLift (f : H →ₜ* X.groupType)
    (h : Y ⟶ X) (k : Y.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) :
    spectrumFunctor.map (restrictionLift f h k hgroup) =
      spectrumRestrictionLift f (spectrumFunctor.map h) k hgroup := by
  apply Langlands.Topology.VariableContinuousAction.Hom.ext
  · exact (spectrumRestrictionLift_groupHom f (spectrumFunctor.map h) k hgroup).symm
  · exact (spectrumFunctor_restrictionLift_spaceMap f h k hgroup).trans
      (spectrumRestrictionLift_spaceMap f (spectrumFunctor.map h) k hgroup).symm

end Restriction

end Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace
