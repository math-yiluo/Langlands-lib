import Langlands.Geometry.Building.KPCentralizerCompatibility
import Langlands.GroupScheme.Rational.SplitTorus

/-!
# Uniqueness of the full omega-compatible apartment class

A bundled form of KP Proposition 6.2.6. This is a proposition, not a proof.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

/-- For a maximal split torus of a connected reductive group over a nonarchimedean
local field, two full omega-compatible equipollence classes are equal
(KP Proposition 6.2.6 and Definition 6.1.7). -/
def OmegaCompatibleApartmentUniquenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
      [Mono i.hom.hom.left],
      IsMaximalSplitTorus i →
      ∀ (C : CentralizerDatum i)
        (D E : KPApartmentData i (localFieldOrder F)),
        D.IsOmegaCompatible C → E.IsOmegaCompatible C → D = E

end Langlands.Geometry.Building
