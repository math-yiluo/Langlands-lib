import Langlands.GroupScheme.IntegralModel.UnramifiedIntegralPointAction
import Langlands.GroupScheme.IntegralModel.Iso

/-! # Unramified descent of smooth integral models (KP Fact 2.10.16) -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

/-- The necessary direction of KP Fact 2.10.16: a model over the maximal
unramified integers that is isomorphic, over the identity of the generic group,
to the base change of a model over `𝒪[F]` has an integral-point image stable
under every automorphism of the inertia fixed field over `F`. -/
theorem galois_stable_of_iso_baseChangeUnramified
    (M : IntegralModel ↥𝒪[F] F G)
    {M' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G)}
    (e : M.baseChangeUnramified.Iso M' (CategoryTheory.Iso.refl _))
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    {g : rationalPoints (baseChanged F (inertiaFixedField F) G)}
    (hg : g ∈ M'.integralPoints) :
    rationalConjugate F (inertiaFixedField F) G σ g ∈ M'.integralPoints := by
  rw [← e.integralPoints_eq] at hg ⊢
  exact (M.mem_baseChangeUnramified_integralPoints_rationalConjugate_iff σ g).mpr hg

/-- **KP Fact 2.10.16 for group-scheme models over a nonarchimedean local field.**
Let `M'` be a smooth integral model, over the integers of the maximal
unramified extension, of the base change of `G`. If its integral-point image is
stable under every automorphism of the inertia fixed field over `F`, then `M'`
descends: there is a smooth integral model `M` of `G` over `𝒪[F]` whose
unramified base change is isomorphic to `M'` over the identity of the generic
group. -/
def UnramifiedSmoothModelDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (M' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G)),
    M'.IsSmooth →
    (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ∀ g ∈ M'.integralPoints,
        rationalConjugate F (inertiaFixedField F) G σ g ∈ M'.integralPoints) →
    ∃ M : IntegralModel ↥𝒪[F] F G, M.IsSmooth ∧
      Nonempty (M.baseChangeUnramified.Iso M' (CategoryTheory.Iso.refl _))

end Langlands.GroupScheme.IntegralModel
