import Langlands.GroupScheme.IntegralModel.AffineWeilKernelIso
import Langlands.GroupScheme.Examples.SU3RootUnitaryIntegralModel

/-! # Actual restricted unitary depth-transition kernels on field fibres -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

local instance {O K : Type u} [CommRing O] [IsDomain O] [Field K]
    [Algebra O K] [IsFractionRing O K] {G : GroupScheme (Spec (CommRingCat.of K))}
    (P : IntegralModel O K G) : IsAffine P.group.X.left :=
  isAffine_of_isAffineHom P.group.X.hom

namespace SU3Root.IntegralChart

open BilinearCoordinate IntegralModel

variable (A k : Type u) [CommRing A] [Field k] [Algebra A k]
  {O K L : Type u} [CommRing O] [IsDomain O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  [Algebra A O] [Module.Finite A O] [Module.Projective A O]
  {I J : Type u} [Fintype I] [Fintype J]
  (C : IntegralChart O K L I) (C' : IntegralChart O K L J)
  (M : I → J → O) (t : O)
  (h : C.data.IsChartChange C'.data
    (fun i j => algebraMap O K (M i j)) (algebraMap O K t))

attribute [local instance] AffineWeilBilinear.bilinear_isAffine
  AffineWeilBilinear.bilinear_locallyOfFiniteType Algebra.TensorProduct.rightAlgebra

/-- Every extension of the generic identity, after actual restriction and field base
change, has the explicit restricted bilinear fibre kernel. -/
def weilFibreKernelIso
    (φ : C.model.Hom C'.model (𝟙 (unitaryParameterGroup K L))) :
    kernel (AffineWeil.BaseChange.sourceMap A O k C.model.group φ.hom) ≅
      kernel (AffineWeil.map k (k ⊗[A] O)
        (BilinearCoordinate.linearHom (CommRingCat.of (k ⊗[A] O))
          (fun i j => algebraMap O (k ⊗[A] O) (M i j))
          (algebraMap O (k ⊗[A] O) t)
          ((C.isCompatible_of_isChartChange C' M t h).map (algebraMap O (k ⊗[A] O))))) := by
  rw [φ.hom_eq (C.chartHom C' M t h)]
  exact AffineWeilBilinear.linearKernelFibreIso A O k M t
    (C.isCompatible_of_isChartChange C' M t h)

include h in
/-- The actual field-fibre kernel of a restricted generic-identity extension between
integral unitary charts is smooth, connected and unipotent. -/
theorem weilFibre_kernel_properties
    (φ : C.model.Hom C'.model (𝟙 (unitaryParameterGroup K L))) :
    Smooth (kernel (AffineWeil.BaseChange.sourceMap A O k C.model.group φ.hom)).X.hom ∧
      ConnectedSpace (kernel (AffineWeil.BaseChange.sourceMap A O k C.model.group φ.hom)).X.left ∧
        IsUnipotent (kernel (AffineWeil.BaseChange.sourceMap A O k C.model.group φ.hom)) := by
  rw [φ.hom_eq (C.chartHom C' M t h)]
  exact AffineWeilBilinear.linearKernelFibre_properties A O k M t
    (C.isCompatible_of_isChartChange C' M t h)

variable {P Q : IntegralModel O K (unitaryParameterGroup K L)}

/-- Alternative compatible unitary model presentations retain the explicit restricted
field-fibre kernel. -/
def weilFibrePresentationKernelIso
    (e : P.Iso C.model (CategoryTheory.Iso.refl _))
    (d : Q.Iso C'.model (CategoryTheory.Iso.refl _))
    (φ : P.Hom Q (𝟙 (unitaryParameterGroup K L))) :
    kernel (AffineWeil.BaseChange.sourceMap A O k P.group φ.hom) ≅
      kernel (AffineWeil.map k (k ⊗[A] O)
        (BilinearCoordinate.linearHom (CommRingCat.of (k ⊗[A] O))
          (fun i j => algebraMap O (k ⊗[A] O) (M i j))
          (algebraMap O (k ⊗[A] O) t)
          ((C.isCompatible_of_isChartChange C' M t h).map (algebraMap O (k ⊗[A] O))))) :=
  (e.weilFibreKernelIso A k d φ (C.chartHom C' M t h)) ≪≫
    C.weilFibreKernelIso A k C' M t h (C.chartHom C' M t h)

include h in
/-- All three kernel properties hold for every explicitly compatible presentation before
restriction and every extension of the generic identity. -/
theorem weilFibre_presentation_kernel_properties
    (e : P.Iso C.model (CategoryTheory.Iso.refl _))
    (d : Q.Iso C'.model (CategoryTheory.Iso.refl _))
    (φ : P.Hom Q (𝟙 (unitaryParameterGroup K L))) :
    Smooth (kernel (AffineWeil.BaseChange.sourceMap A O k P.group φ.hom)).X.hom ∧
      ConnectedSpace (kernel (AffineWeil.BaseChange.sourceMap A O k P.group φ.hom)).X.left ∧
        IsUnipotent (kernel (AffineWeil.BaseChange.sourceMap A O k P.group φ.hom)) :=
  e.weilFibreKernel_properties A k d φ (C.chartHom C' M t h)
    (C.weilFibre_kernel_properties A k C' M t h (C.chartHom C' M t h))

end SU3Root.IntegralChart

namespace SU3Root.IsRamifiedQuadraticValuation

variable (A k : Type u) [CommRing A] [Field k] [Algebra A k]
  {O K L : Type u} [CommRing O] [IsDomain O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  [Algebra A O] [Module.Finite A O] [Module.Projective A O]
  {ω : AddValuation L (WithTop ℝ)}
  (hω : IsRamifiedQuadraticValuation K L ω)
  (hO : IsValuationIntegers O K ω)

/-- **Restricted unitary depth-transition kernels.** Every generic-identity extension
between coordinatewise ordered actual lattice depths has a smooth, connected, unipotent
kernel after restriction of scalars and field base change. Equal depths are allowed. -/
theorem lattice_weilFibre_kernel_properties {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (φ : (hω.latticeModel hO r₂ s₂).Hom (hω.latticeModel hO r₁ s₁) (𝟙 _)) :
    Smooth (kernel (AffineWeil.BaseChange.sourceMap A O k
      (hω.latticeModel hO r₂ s₂).group φ.hom)).X.hom ∧
      ConnectedSpace (kernel (AffineWeil.BaseChange.sourceMap A O k
        (hω.latticeModel hO r₂ s₂).group φ.hom)).X.left ∧
        IsUnipotent (kernel (AffineWeil.BaseChange.sourceMap A O k
          (hω.latticeModel hO r₂ s₂).group φ.hom)) :=
  (hω.latticeChart hO r₂ s₂).weilFibre_kernel_properties A k
    (hω.latticeChart hO r₁ s₁) (hω.transitionMatrix hO r₁ r₂)
    (hω.transitionScalar hO r₁ s₁ r₂ s₂) (hω.isChartChange_transition hO hr hs) φ

/-- The explicitly constructed ordered-depth transition has the actual restricted
field-fibre kernel properties. -/
theorem latticeTransition_weilFibre_kernel_properties {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :
    Smooth (kernel (AffineWeil.BaseChange.sourceMap A O k
      (hω.latticeModel hO r₂ s₂).group (hω.latticeTransition hO hr hs).hom)).X.hom ∧
      ConnectedSpace (kernel (AffineWeil.BaseChange.sourceMap A O k
        (hω.latticeModel hO r₂ s₂).group (hω.latticeTransition hO hr hs).hom)).X.left ∧
        IsUnipotent (kernel (AffineWeil.BaseChange.sourceMap A O k
          (hω.latticeModel hO r₂ s₂).group (hω.latticeTransition hO hr hs).hom)) :=
  hω.lattice_weilFibre_kernel_properties A k hO hr hs _

end SU3Root.IsRamifiedQuadraticValuation

end Langlands.GroupScheme
