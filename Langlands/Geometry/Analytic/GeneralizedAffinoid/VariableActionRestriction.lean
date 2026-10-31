import Langlands.Geometry.Analytic.GeneralizedAffinoid.VariableAction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectrumRestriction

/-! # Canonical group restriction and factorization of actual quotient arrows -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

namespace VariableActionSpace

section Restriction

variable (X : VariableActionSpace.{u, v} K)
  {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restrict the actual quotient action without changing its algebra or norm. -/
def restrict (f : H →ₜ* X.groupType) : VariableActionSpace.{u, v} K :=
  ⟨H, (NormContinuousAction.restrict f).obj X.algebraAction⟩

@[simp]
theorem restrict_algebra (f : H →ₜ* X.groupType) :
    (restrict X f).algebraAction.obj.V = X.algebraAction.obj.V := rfl

/-- The canonical geometric arrow has group map `f` and bounded identity pullback. -/
def restrictionMap (f : H →ₜ* X.groupType) : restrict X f ⟶ X where
  groupHom := f
  algebraMap := BoundedAlgHom.id K X.algebraAction.obj.V
  equivariant _ _ := rfl

@[simp]
theorem restrictionMap_groupHom (f : H →ₜ* X.groupType) :
    (restrictionMap X f).groupHom = f := rfl

@[simp]
theorem restrictionMap_algebraMap (f : H →ₜ* X.groupType) :
    (restrictionMap X f).algebraMap = BoundedAlgHom.id K X.algebraAction.obj.V := rfl

/-- Identity restriction is isomorphic by identity bounded maps; its forward
arrow is precisely the canonical restriction arrow. -/
def restrictIdIso : restrict X (ContinuousMonoidHom.id X.groupType) ≅ X where
  hom := restrictionMap X (ContinuousMonoidHom.id X.groupType)
  inv :=
    { groupHom := ContinuousMonoidHom.id X.groupType
      algebraMap := BoundedAlgHom.id K X.algebraAction.obj.V
      equivariant _ _ := rfl }
  hom_inv_id := by apply Hom.ext <;> rfl
  inv_hom_id := by apply Hom.ext <;> rfl

@[simp]
theorem restrictIdIso_hom :
    (restrictIdIso X).hom = restrictionMap X (ContinuousMonoidHom.id X.groupType) := rfl

variable {J : Type v} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]

/-- Successive and composite restriction have identity group and algebra
comparison maps on the retained quotient. -/
def restrictCompIso (f : H →ₜ* X.groupType) (g : J →ₜ* H) :
    restrict (restrict X f) g ≅ restrict X (f.comp g) where
  hom :=
    { groupHom := ContinuousMonoidHom.id J
      algebraMap := BoundedAlgHom.id K X.algebraAction.obj.V
      equivariant _ _ := rfl }
  inv :=
    { groupHom := ContinuousMonoidHom.id J
      algebraMap := BoundedAlgHom.id K X.algebraAction.obj.V
      equivariant _ _ := rfl }
  hom_inv_id := by apply Hom.ext <;> rfl
  inv_hom_id := by apply Hom.ext <;> rfl

/-- The comparison identifies the successive canonical arrows with the
canonical arrow for the composed group homomorphism. -/
theorem restrictionMap_comp (f : H →ₜ* X.groupType) (g : J →ₜ* H) :
    (restrictCompIso X f g).hom ≫ restrictionMap X (f.comp g) =
      restrictionMap (restrict X f) g ≫ restrictionMap X f := by
  apply Hom.ext <;> rfl

end Restriction

section Factorization

variable {X Y : VariableActionSpace.{u, v} K}

/-- The fixed-source-group part of a varying-group geometric arrow, constructed
from its existing equivariant algebra arrow after target restriction. -/
def fixedFactor (f : X ⟶ Y) : X ⟶ restrict Y f.groupHom :=
  (ofFixed X.groupType).map (Quiver.Hom.op (restrictedAlgebraHom f))

@[simp]
theorem fixedFactor_groupHom (f : X ⟶ Y) :
    (fixedFactor f).groupHom = ContinuousMonoidHom.id X.groupType := rfl

@[simp]
theorem fixedFactor_algebraMap (f : X ⟶ Y) :
    (fixedFactor f).algebraMap = f.algebraMap := rfl

/-- Every varying-group arrow factors through restriction to its source group. -/
theorem fixedFactor_comp_restrictionMap (f : X ⟶ Y) :
    fixedFactor f ≫ restrictionMap Y f.groupHom = f := by
  apply Hom.ext <;> rfl

/-- The fixed-group part is unique among arrows with identity source-group map. -/
theorem fixedFactor_unique (f : X ⟶ Y) (h : X ⟶ restrict Y f.groupHom)
    (hgroup : h.groupHom = ContinuousMonoidHom.id X.groupType)
    (hfactor : h ≫ restrictionMap Y f.groupHom = f) : h = fixedFactor f := by
  apply Hom.ext
  · exact hgroup
  · exact congrArg (fun k : X ⟶ Y => k.algebraMap) hfactor

end Factorization

section Spectrum

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Taking actual continuous spectra commutes exactly with the fixed-group
embedding, on both the retained group and the continuous seminorm maps. -/
theorem ofFixed_comp_spectrumFunctor :
    ofFixed (K := K) G ⋙ spectrumFunctor =
      NormContinuousAction.spectrumFunctor ⋙
        Langlands.Topology.VariableContinuousAction.ofFixed G := rfl

variable {G}
  (X : VariableActionSpace.{u, v} K)
  {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Reuse the existing identity-on-seminorms comparison with restriction of the
original jointly continuous spectrum action. -/
def spectrumRestrictIso (f : H →ₜ* X.groupType) :
    spectrumFunctor.obj (restrict X f) ≅
      (Langlands.Topology.VariableContinuousAction.ofFixed H).obj
        ((ContAction.res TopCat f).obj (NormContinuousAction.spectrum X.algebraAction)) :=
  (Langlands.Topology.VariableContinuousAction.ofFixed H).mapIso
    (NormContinuousAction.spectrumRestrictIso f X.algebraAction)

@[simp]
theorem spectrumRestrictIso_hom_apply (f : H →ₜ* X.groupType)
    (x : BanachSpectrum X.algebraAction.obj.V) :
    (spectrumRestrictIso X f).hom.spaceMap x = x := rfl

@[simp]
theorem spectrumRestrictIso_inv_apply (f : H →ₜ* X.groupType)
    (x : BanachSpectrum X.algebraAction.obj.V) :
    (spectrumRestrictIso X f).inv.spaceMap x = x := rfl

@[simp]
theorem spectrumFunctor_restrictionMap_apply (f : H →ₜ* X.groupType)
    (x : BanachSpectrum X.algebraAction.obj.V) :
    (spectrumFunctor.map (restrictionMap X f)).spaceMap x = x :=
  BanachSpectrum.ext fun _ => rfl

variable {X} {Y : VariableActionSpace.{u, v} K}

/-- The fixed-group spectrum map is exactly the first factor of the
varying-group spectrum map. -/
theorem spectrumFunctor_fixedFactor (f : X ⟶ Y) :
    spectrumFunctor.map (fixedFactor f) =
      (Langlands.Topology.VariableContinuousAction.ofFixed X.groupType).map
        (NormContinuousAction.spectrumFunctor.map
          (Quiver.Hom.op (restrictedAlgebraHom f))) := rfl

/-- Actual continuous spectra carry the geometric restriction factorization to
the corresponding factorization with the original group homomorphism. -/
theorem spectrumFunctor_factorization (f : X ⟶ Y) :
    (Langlands.Topology.VariableContinuousAction.ofFixed X.groupType).map
        (NormContinuousAction.spectrumFunctor.map
          (Quiver.Hom.op (restrictedAlgebraHom f))) ≫
      spectrumFunctor.map (restrictionMap Y f.groupHom) = spectrumFunctor.map f := by
  change spectrumFunctor.map (fixedFactor f) ≫
    spectrumFunctor.map (restrictionMap Y f.groupHom) = spectrumFunctor.map f
  rw [← Functor.map_comp, fixedFactor_comp_restrictionMap]

end Spectrum

end VariableActionSpace

end Langlands.Analytic.PresentedAffinoidAlgebra
