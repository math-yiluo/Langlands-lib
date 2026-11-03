import Langlands.BruhatTits.Cartan.CentralizerTorusValuation
import Langlands.Geometry.Building.KPCentralizerCompatibility

/-! # Statement targets for the split-torus consequence of full V6 -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.Cartan

/-- For the actual represented centralizer of a maximal split torus, full V6
implies its split-torus part, with the identity character comparison explicit.
This is a conditional statement target, not an existence assertion for data. -/
def CentralizerSplitCompatibilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∀ (C : CentralizerDatum i),
        Function.Bijective (restrictionEvaluation (𝟙 S.toGrp)) →
        ∀ φ : RootFunctionFamily S G,
          IsCentralizerCompatible i C.j C.s C.bijective φ →
            IsSplitTorusCompatible i (localFieldOrder F) φ

/-- The actual finite coordinate split-torus version has no additional
identity character-comparison hypothesis. It retains the same represented
centralizer, actual maximal inclusion and full-V6 premise. -/
def CoordinateCentralizerSplitCompatibilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (I : Type u) [Finite I]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsConnectedReductive G →
    ∀ (i : (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I).toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∀ (C : CentralizerDatum i)
        (φ : RootFunctionFamily (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I) G),
        IsCentralizerCompatible i C.j C.s C.bijective φ →
          IsSplitTorusCompatible i (localFieldOrder F) φ

end Langlands.BruhatTits.Cartan
