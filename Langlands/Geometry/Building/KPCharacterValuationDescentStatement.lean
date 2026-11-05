import Langlands.Geometry.Building.KPZeroNormKernel

/-! # Descent of the character-valuation kernel from `K` to `F` (KP 2.6.16(4), 2.6.17) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- For an affine `F`-group `G`, `G(F)^1 = G(K)^1 ∩ G(F)`. -/
def CharacterValuationKernelDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left],
    (characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F)
        (GaloisPointComparison.baseChanged F (UnramifiedClosure F) G)).comap
      (GaloisPointComparison.rationalExtend F (UnramifiedClosure F) G) =
    Plancherel.rationalCommonNormKernel G

end Langlands.Geometry.Building
