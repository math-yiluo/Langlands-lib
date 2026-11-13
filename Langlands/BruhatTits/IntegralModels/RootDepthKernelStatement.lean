import Langlands.BruhatTits.IntegralModels.RootFiltrationModel
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.AbelianScheme.Kernel
import Langlands.GroupScheme.Reductive.Basic

/-! # Kernels between actual root-depth models over the maximal unramified integers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- **KP Lemma C.5.3, invariant under the supplied root-model presentations.**
For two smooth connected integral models of the same actual relative root
subgroup at depths `r ≤ s`, every model map from depth `s` to depth `r`
whose generic map commutes with the inclusions into `G` has a smooth,
connected and unipotent scheme-theoretic kernel on special fibres.

This target is over the actual maximal unramified integers of a local field.
The root models and compatible model map are quantified inputs; their
existence is not part of this statement. -/
def UnramifiedRootDepthKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom] (C : MaximalUnramified.BuildingData F G)
    (x : C.Apartment) (a : relativeRoots C.i) (r s : ℝ),
    r ≤ s →
    ∀ (U : RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
        C.apartment x a r)
      (V : RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
        C.apartment x a s)
      (f : V.rootGroup ⟶ U.rootGroup),
      f ≫ U.inclusion = V.inclusion →
      ∀ φ : V.model.Hom U.model f,
        Smooth (kernel φ.specialFibreMap).X.hom ∧
          ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
            IsUnipotent (kernel φ.specialFibreMap)

end Langlands.BruhatTits.IntegralModels
