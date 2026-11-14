import Langlands.GroupScheme.AffineWeilBilinearFibres
import Langlands.GroupScheme.IntegralModel.AffineWeil
import Langlands.GroupScheme.Examples.SU3RootUnitaryWeilKernel

/-! # Actual restricted integral unitary models and special-fibre kernels -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SU3Root.IntegralChart

variable (A F : Type u) [CommRing A] [IsDomain A] [Field F]
  [Algebra A F] [IsFractionRing A F]
  {O K L : Type u} [CommRing O] [IsDomain O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  [Algebra A O] [Module.Finite A O] [Module.Projective A O]
  {I J : Type u} [Fintype I] [Fintype J]
  (C : IntegralChart O K L I) (C' : IntegralChart O K L J)
  {G H : GroupScheme (Spec (CommRingCat.of F))}

local instance (P : IntegralModel O K (unitaryParameterGroup K L)) :
    IsAffine P.group.X.left :=
  isAffine_of_isAffineHom P.group.X.hom

local instance (C : IntegralChart O K L I) : Smooth C.model.group.X.hom :=
  C.model_isSmooth

/-- The original unitary chart restricted from O to A, with an explicitly supplied
generic identification over the fraction field of A. -/
def weilModel (e : AffineWeil.BaseChange.source A O F C.model.group ≅ G) :
    IntegralModel A F G :=
  IntegralModel.affineWeil A F O C.model.group e

theorem weilModel_isSmooth
    (e : AffineWeil.BaseChange.source A O F C.model.group ≅ G) :
    (C.weilModel A F e).IsSmooth :=
  IntegralModel.affineWeil_isSmooth A F O C.model.group e

theorem weilModel_hasGeometricallyConnectedFibres
    (e : AffineWeil.BaseChange.source A O F C.model.group ≅ G) :
    (C.weilModel A F e).HasGeometricallyConnectedFibres :=
  AffineWeilBilinear.restriction_geometricallyConnected A O C.coeff

variable (M : I → J → O) (t : O)
  (h : C.data.IsChartChange C'.data
    (fun i j => algebraMap O K (M i j)) (algebraMap O K t))
  (e : AffineWeil.BaseChange.source A O F C.model.group ≅ G)
  (d : AffineWeil.BaseChange.source A O F C'.model.group ≅ H)
  {f : G ⟶ H}
  (hf : AffineWeil.BaseChange.sourceMap A O F C.model.group
      (C.chartHom C' M t h).hom ≫ d.hom = e.hom ≫ f)

/-- Actual restriction of the explicit unitary chart change, with the stated
generic map under the original generic identifications. -/
def weilModelHom : (C.weilModel A F e).Hom (C'.weilModel A F d) f :=
  IntegralModel.affineWeilHom A F O e d (C.chartHom C' M t h).hom hf

variable [IsLocalRing A]

include hf in
/-- Every compatible extension between the actual restricted integral unitary models
has a smooth, connected, unipotent special-fibre kernel over the residue field of A. -/
theorem weilModel_kernel_properties
    (φ : (C.weilModel A F e).Hom (C'.weilModel A F d) f) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  rw [IntegralModel.affineWeil_specialFibreMap_eq A F O e d
    (C.chartHom C' M t h).hom hf φ]
  exact C.weilFibre_kernel_properties A (IsLocalRing.ResidueField A) C' M t h
    (C.chartHom C' M t h)

include hf in
/-- Compatible arbitrary presentations over the restriction base retain the actual
special-fibre kernel properties of the restricted chart transition. -/
theorem weilModel_presentation_kernel_properties
    {P : IntegralModel A F G} {Q : IntegralModel A F H}
    (ep : P.Iso (C.weilModel A F e) (CategoryTheory.Iso.refl G))
    (dq : Q.Iso (C'.weilModel A F d) (CategoryTheory.Iso.refl H))
    (φ : P.Hom Q f) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  ep.specialFibreKernel_properties dq φ (C.weilModelHom A F C' M t h e d hf)
    (C.weilModel_kernel_properties A F C' M t h e d hf
      (C.weilModelHom A F C' M t h e d hf))

end Langlands.GroupScheme.SU3Root.IntegralChart
