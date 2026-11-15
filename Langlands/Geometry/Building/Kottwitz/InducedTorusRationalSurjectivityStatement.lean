import Langlands.Geometry.Building.Kottwitz.TorusMap
import Langlands.GroupScheme.Torus.Induced

/-! # KP Corollary 11.1.9: the rational Kottwitz map of an induced torus is surjective -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

/-- KP Corollary 11.1.9: for every induced torus `T` over a nonarchimedean local field `F`,
the constructed rational torus Kottwitz homomorphism
`torusKottwitzRational F T : T(F) → X_*(T)_I^Γ`, with `I` the inertia group of `F^sep/K`,
`Γ = Gal(K/F)` and `K = UnramifiedClosure F`, is surjective. -/
def InducedTorusKottwitzRationalSurjectivityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (hT : IsInducedTorus T),
    Function.Surjective (torusKottwitzRational F T hT.isTorus)

end Langlands.Geometry.Building.Kottwitz
