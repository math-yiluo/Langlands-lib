import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelBaseChange
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelIso
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.IntegralModel.FixedFieldExtension
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.BruhatTits.IntegralModels.ModelMorphism

/-! # Full special-fibre kernels from characterized unramified models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel

namespace Langlands.GroupScheme.IntegralModel

open Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {M N : IntegralModel ↥𝒪[F] F G}

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

/-- The actual unramified coefficient extension of an identity-generic model
map, with the generic map written as the identity. -/
def Hom.baseChangeUnramifiedId (φ : M.Hom N (𝟙 G)) :
    M.baseChangeUnramified.Hom N.baseChangeUnramified (𝟙 _) where
  hom := (φ.baseChangeCoefficients (fixedFieldIntegers F) (inertiaFixedField F)).hom
  generic_comm := by
    simpa only [baseChangeUnramified, CategoryTheory.Functor.map_id] using
      (φ.baseChangeCoefficients (fixedFieldIntegers F) (inertiaFixedField F)).generic_comm

/-- The changed identity-generic map is the original map pulled back to the
actual maximal-unramified integers. -/
theorem Hom.baseChangeUnramifiedId_hom (φ : M.Hom N (𝟙 G)) :
    φ.baseChangeUnramifiedId.hom =
      (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map φ.hom :=
  rfl

/-- Equal integral-point images identify a smooth model over the actual
maximal-unramified integers with the coefficient extension of a smooth model. -/
def unramifiedIsoOfIntegralPointsEq
    (M : IntegralModel ↥𝒪[F] F G)
    (Q : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hM : M.IsSmooth) (hQ : Q.IsSmooth)
    (hpoints : M.baseChangeUnramified.integralPoints = Q.integralPoints) :
    M.baseChangeUnramified.Iso Q (CategoryTheory.Iso.refl _) :=
  isoOfIntegralPointsEq M.baseChangeUnramified Q
    (fixedField_hasSmoothHomExtension smoothHomExtension F)
    (M.isSmooth_baseChange (fixedFieldIntegers F) (inertiaFixedField F) hM) hQ hpoints

/-- Full-kernel geometry of any homomorphism between characterized smooth
unramified models descends to the original identity-generic model map. -/
theorem Hom.specialFibreKernel_properties_of_unramifiedModels
    (φ : M.Hom N (𝟙 G))
    (Q P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hM : M.IsSmooth) (hN : N.IsSmooth) (hQ : Q.IsSmooth) (hP : P.IsSmooth)
    (hsource : M.baseChangeUnramified.integralPoints = Q.integralPoints)
    (htarget : N.baseChangeUnramified.integralPoints = P.integralPoints)
    (ψ : Q.Hom P (𝟙 _))
    (hψ : Smooth (kernel ψ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel ψ.specialFibreMap).X.left ∧
        IsUnipotent (kernel ψ.specialFibreMap)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  have h := Iso.specialFibreKernel_properties
    (M.unramifiedIsoOfIntegralPointsEq Q hM hQ hsource)
    (N.unramifiedIsoOfIntegralPointsEq P hN hP htarget)
    φ.baseChangeUnramifiedId ψ hψ
  exact φ.specialFibreKernel_properties_of_baseChange
    (fixedFieldIntegers F) (inertiaFixedField F) h

end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {source target : RelativeComponentModelData ↥𝒪[F] F G}

/-- The kernel clause for a supplied relative-component map follows from
the full kernel of any identity-generic map between smooth unramified models
with the same two characterized integral-point images. -/
theorem hasSmoothConnectedUnipotentKernel_of_unramifiedModels
    (φ : RelativeComponentModelHom source target)
    (Q P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hQ : Q.IsSmooth) (hP : P.IsSmooth)
    (hsource : source.neutral.baseChangeUnramified.integralPoints = Q.integralPoints)
    (htarget : target.neutral.baseChangeUnramified.integralPoints = P.integralPoints)
    (ψ : Q.Hom P (𝟙 _))
    (hψ : Smooth (kernel ψ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel ψ.specialFibreMap).X.left ∧
        IsUnipotent (kernel ψ.specialFibreMap)) :
    φ.HasSmoothConnectedUnipotentKernel :=
  φ.neutral.specialFibreKernel_properties_of_unramifiedModels Q P
    source.neutral_smooth target.neutral_smooth hQ hP hsource htarget ψ hψ

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom
