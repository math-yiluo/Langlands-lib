import Langlands.Geometry.Building.UnramifiedFixedPointStabilizer
import Langlands.Geometry.Building.MaximalUnramifiedValuation

/-! # Galois stability of the maximal-unramified character-valuation kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-- Coefficient conjugation preserves and reflects the character-valuation
kernel over the maximal unramified field. -/
theorem unramified_characterValuationKernel_galois_iff
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F)
    (x : rationalPoints (baseChanged F (UnramifiedClosure F) G)) :
    rationalConjugate F (UnramifiedClosure F) G σ x ∈
        characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (UnramifiedClosure F) G) ↔
      x ∈ characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (UnramifiedClosure F) G) :=
  rationalConjugate_mem_characterValuationKernel_iff F (UnramifiedClosure F) G
    (MaximalUnramified.valuation F) σ (MaximalUnramified.valuation_galois F σ) x

/-- Galois stability of `G(K)^1`, strengthened to preservation and reflection,
for every group scheme over the local field. -/
def UnramifiedCharacterValuationKernelGaloisStabilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F)
    (x : rationalPoints (baseChanged F (UnramifiedClosure F) G)),
    rationalConjugate F (UnramifiedClosure F) G σ x ∈
        characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (UnramifiedClosure F) G) ↔
      x ∈ characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (UnramifiedClosure F) G)

/-- Specialize coefficient stability for an invariant valuation to the
Galois-invariant valuation on the maximal unramified field. -/
theorem unramifiedCharacterValuationKernelGaloisStability :
    UnramifiedCharacterValuationKernelGaloisStabilityStatement.{u} :=
  unramified_characterValuationKernel_galois_iff

end Langlands.Geometry.Building
