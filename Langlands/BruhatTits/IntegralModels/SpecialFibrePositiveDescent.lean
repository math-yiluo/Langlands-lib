import Langlands.BruhatTits.IntegralModels.DepthZeroReduction
import Langlands.GroupScheme.IntegralModel.UnramifiedReductionPoints

/-! # Unramified descent of the positive subgroup of a supplied quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData

open GroupScheme

section Local

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)

/-- The positive subgroup is the generic image of the kernel of reduction
followed by the supplied quotient projection. -/
theorem positivePoints_eq_specialFibreKernelPoints
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    Q.positivePoints = D.neutral.specialFibreKernelPoints Q.projection := by
  change Q.positiveSections.map D.neutral.integralPointMap =
    ((rationalPoints.map Q.projection).comp D.neutral.reduction).ker.map
      D.neutral.integralPointMap
  rw [← Q.ker_reductiveReduction hQ]
  rfl

end Local

open Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {D : RelativeComponentModelData ↥𝒪[F] F G} (Q : SpecialFibreQuotientData D)

/-- Over the actual maximal unramified extension, the generic image of the
kernel of the scalar-extended quotient projection after reduction. -/
def unramifiedKernelPoints :
    Subgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)) :=
  D.neutral.baseChangeUnramified.specialFibreKernelPoints
    (D.neutral.unramifiedSpecialFibreMap Q.projection)

/-- The supplied positive subgroup is the exact preimage of the extended
quotient-kernel subgroup under actual maximal-unramified extension. -/
theorem positivePoints_eq_comap_unramifiedKernelPoints
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection) :
    Q.positivePoints = Q.unramifiedKernelPoints.comap
      (rationalExtend F (inertiaFixedField F) G) := by
  rw [Q.positivePoints_eq_specialFibreKernelPoints hQ]
  exact D.neutral.specialFibreKernelPoints_eq_comap_unramified Q.projection

end Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData
