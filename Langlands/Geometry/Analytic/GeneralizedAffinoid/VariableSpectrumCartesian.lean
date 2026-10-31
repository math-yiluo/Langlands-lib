import Langlands.Geometry.Analytic.GeneralizedAffinoid.VariableSpectrumFibered

/-! # Cartesian quotient arrows and their actual spectra -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {X Y : VariableActionSpace.{u, v} K}

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

/-- A Cartesian quotient arrow identifies its source with canonical restriction. -/
def cartesianRestrictionIso (h : X ⟶ Y)
    [Functor.IsCartesian groupForget (groupForget.map h) h] :
    X ≅ restrict Y h.groupHom := by
  have hc : Functor.IsCartesian groupForget (groupForget.map h)
      (restrictionMap Y h.groupHom) :=
    @Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _
      groupForget (groupForget.obj X) (groupForget.obj Y) _ _
      (groupForget.map h) (restrictionMap Y h.groupHom)
      (restrictionMap_isStronglyCartesian Y (groupForget.obj X) (groupForget.map h))
  exact Functor.IsCartesian.domainUniqueUpToIso groupForget (groupForget.map h)
    (restrictionMap Y h.groupHom) h

@[simp]
theorem cartesianRestrictionIso_hom_groupHom (h : X ⟶ Y)
    [Functor.IsCartesian groupForget (groupForget.map h) h] :
    (cartesianRestrictionIso h).hom.groupHom = ContinuousMonoidHom.id X.groupType := by
  have hc : Functor.IsCartesian groupForget (groupForget.map h)
      (restrictionMap Y h.groupHom) :=
    @Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _
      groupForget (groupForget.obj X) (groupForget.obj Y) _ _
      (groupForget.map h) (restrictionMap Y h.groupHom)
      (restrictionMap_isStronglyCartesian Y (groupForget.obj X) (groupForget.map h))
  have hlift : Functor.IsHomLift groupForget (𝟙 (groupForget.obj X))
      (cartesianRestrictionIso h).hom :=
    Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift groupForget
      (groupForget.map h) (restrictionMap Y h.groupHom) h
  exact (@IsHomLift.eq_of_isHomLift _ _ _ _ (groupForget (K := K))
    X (restrict Y h.groupHom) (𝟙 (groupForget.obj X))
    (cartesianRestrictionIso h).hom hlift).symm

/-- The comparison factors the complete original quotient arrow. -/
@[reassoc]
theorem cartesianRestrictionIso_hom_comp (h : X ⟶ Y)
    [Functor.IsCartesian groupForget (groupForget.map h) h] :
    (cartesianRestrictionIso h).hom ≫ restrictionMap Y h.groupHom = h := by
  have hc : Functor.IsCartesian groupForget (groupForget.map h)
      (restrictionMap Y h.groupHom) :=
    @Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _
      groupForget (groupForget.obj X) (groupForget.obj Y) _ _
      (groupForget.map h) (restrictionMap Y h.groupHom)
      (restrictionMap_isStronglyCartesian Y (groupForget.obj X) (groupForget.map h))
  exact Functor.IsCartesian.fac groupForget (groupForget.map h) (restrictionMap Y h.groupHom) h

/-- The actual spectrum of every Cartesian quotient arrow is strongly Cartesian. -/
instance spectrumFunctor_map_isStronglyCartesian (h : X ⟶ Y)
    [Functor.IsCartesian groupForget (groupForget.map h) h] :
    Functor.IsStronglyCartesian
      Langlands.Topology.VariableContinuousAction.groupForget (groupForget.map h)
      (spectrumFunctor.map h) := by
  let e := spectrumFunctor.mapIso (cartesianRestrictionIso h)
  have heq : Langlands.Topology.VariableContinuousAction.groupForget.map e.hom =
      (𝟙 (groupForget.obj X)) := cartesianRestrictionIso_hom_groupHom h
  have hlift : Functor.IsHomLift
      Langlands.Topology.VariableContinuousAction.groupForget (𝟙 (groupForget.obj X))
      e.hom := by
    rw [← heq]
    exact IsHomLift.map Langlands.Topology.VariableContinuousAction.groupForget e.hom
  have hiso : Functor.IsStronglyCartesian
      Langlands.Topology.VariableContinuousAction.groupForget (𝟙 (groupForget.obj X))
      e.hom :=
    Functor.IsStronglyCartesian.of_iso
      Langlands.Topology.VariableContinuousAction.groupForget (𝟙 (groupForget.obj X)) e
  have hres : Functor.IsStronglyCartesian
      Langlands.Topology.VariableContinuousAction.groupForget (groupForget.map h)
      (spectrumFunctor.map (restrictionMap Y h.groupHom)) :=
    spectrumFunctor_restrictionMap_isStronglyCartesian Y (groupForget.obj X) h.groupHom
  have hc : Functor.IsStronglyCartesian
      Langlands.Topology.VariableContinuousAction.groupForget
      ((𝟙 (groupForget.obj X)) ≫ groupForget.map h)
      (e.hom ≫ spectrumFunctor.map (restrictionMap Y h.groupHom)) :=
    @Functor.IsStronglyCartesian.comp _ _ _ _
      Langlands.Topology.VariableContinuousAction.groupForget
      (groupForget.obj X) (groupForget.obj X) (groupForget.obj Y) _ _ _
      (𝟙 (groupForget.obj X)) h.groupHom e.hom
      (spectrumFunctor.map (restrictionMap Y h.groupHom)) hiso hres
  have hfac : e.hom ≫ spectrumFunctor.map (restrictionMap Y h.groupHom) =
      spectrumFunctor.map h := by
    change spectrumFunctor.map (cartesianRestrictionIso h).hom ≫
      spectrumFunctor.map (restrictionMap Y h.groupHom) = spectrumFunctor.map h
    rw [← Functor.map_comp, cartesianRestrictionIso_hom_comp]
  rw [Category.id_comp, hfac] at hc
  exact hc

end Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace
