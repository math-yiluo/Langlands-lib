import Langlands.Automorphic.GroupSchemeFullAEL2Continuous

/-! # Dense continuous cuspidal classes in closed invariant subspaces -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- The classes of continuous functions with vanishing parabolic constant terms
are norm dense in every closed invariant subspace of the full AE cusp space. -/
def GroupSchemeFullAEL2ContinuousDensityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let ρ := fullAEL2CuspidalRightAction F G hPD hG T i hi I e hc
    let c := positiveParabolicCuspidalL2ToFullAE F G hPD hG T i hi I e hc
    ∀ (P : Submodule ℂ S), IsClosed (P : Set S) →
      (∀ (a : AdelicGroupPoints F G) (φ : S), φ ∈ P → ρ a φ ∈ P) →
      Dense {φ : P | (φ : S) ∈ Set.range c}

end Langlands.Automorphic.GroupSchemeFunctions
