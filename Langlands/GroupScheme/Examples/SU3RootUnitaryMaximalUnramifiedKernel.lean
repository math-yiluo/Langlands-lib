import Langlands.GroupScheme.Examples.SU3RootUnitaryMaximalUnramified
import Langlands.GroupScheme.Examples.SU3RootUnitaryLatticeKernel

/-! # Unitary depth-transition kernels over the actual maximal unramified integers -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open Langlands.LocalGalois.Separable Langlands.Geometry.Building
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SU3Root

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : Type u) [Field L] [Algebra (inertiaFixedField F) L]
  [Algebra.IsQuadraticExtension (inertiaFixedField F) L]
  [Algebra.IsSeparable (inertiaFixedField F) L]

/-- The actual reduced diagonal arrow between the maximal-unramified unitary depth models. -/
abbrev maximalUnramifiedResidueHom {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :=
  (maximalUnramifiedValuation_isRamified F L).latticeResidueHom
    (maximalUnramifiedValuation_isValuationIntegers F L) hr hs

/-- Every extension of the generic identity has the actual reduced diagonal kernel. -/
def maximalUnramifiedSpecialFibreKernelIso {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (φ : (maximalUnramifiedModel F L r₂ s₂).Hom
      (maximalUnramifiedModel F L r₁ s₁) (𝟙 _)) :
    kernel φ.specialFibreMap ≅ kernel (maximalUnramifiedResidueHom F L hr hs) :=
  (maximalUnramifiedValuation_isRamified F L).latticeSpecialFibreKernelIso
    (maximalUnramifiedValuation_isValuationIntegers F L) hr hs φ

/-- **KP Lemma C.4.4 over the actual maximal unramified integers.** Every extension of the
generic identity between coordinatewise ordered unitary depths has a smooth, connected and
unipotent special-fibre kernel. -/
theorem maximalUnramified_specialFibre_kernel_properties {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (φ : (maximalUnramifiedModel F L r₂ s₂).Hom
      (maximalUnramifiedModel F L r₁ s₁) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  (maximalUnramifiedValuation_isRamified F L).lattice_specialFibre_kernel_properties
    (maximalUnramifiedValuation_isValuationIntegers F L) hr hs φ

/-- The explicitly constructed transition has all three actual kernel properties. -/
theorem maximalUnramifiedTransition_kernel_properties {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :
    Smooth (kernel (maximalUnramifiedTransition F L hr hs).specialFibreMap).X.hom ∧
      ConnectedSpace (kernel (maximalUnramifiedTransition F L hr hs).specialFibreMap).X.left ∧
        IsUnipotent (kernel (maximalUnramifiedTransition F L hr hs).specialFibreMap) :=
  maximalUnramified_specialFibre_kernel_properties F L hr hs _

variable {M N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
  (unitaryParameterGroup (inertiaFixedField F) L)}

/-- The kernel comparison is invariant under explicitly compatible model presentations. -/
def maximalUnramifiedPresentationKernelIso {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (e : M.Iso (maximalUnramifiedModel F L r₂ s₂) (CategoryTheory.Iso.refl _))
    (d : N.Iso (maximalUnramifiedModel F L r₁ s₁) (CategoryTheory.Iso.refl _))
    (φ : M.Hom N (𝟙 _)) :
    kernel φ.specialFibreMap ≅ kernel (maximalUnramifiedResidueHom F L hr hs) :=
  (maximalUnramifiedValuation_isRamified F L).latticePresentationKernelIso
    (maximalUnramifiedValuation_isValuationIntegers F L) hr hs e d φ

/-- All three kernel properties hold for every explicitly compatible presentation and every
generic-identity extension over the actual maximal unramified integer ring. -/
theorem maximalUnramified_presentation_kernel_properties {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (e : M.Iso (maximalUnramifiedModel F L r₂ s₂) (CategoryTheory.Iso.refl _))
    (d : N.Iso (maximalUnramifiedModel F L r₁ s₁) (CategoryTheory.Iso.refl _))
    (φ : M.Hom N (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  (maximalUnramifiedValuation_isRamified F L).lattice_presentation_kernel_properties
    (maximalUnramifiedValuation_isValuationIntegers F L) hr hs e d φ

end Langlands.GroupScheme.SU3Root
