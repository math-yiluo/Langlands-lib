import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Compactness of continuous cuspidal convolutions -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global AdelicGroupPoints PositiveRealTorus Langlands.GroupScheme

/-- Every continuous compactly supported weight on the full adelic group
acts by a compact operator on the original full cuspidal `L²` space. -/
def GroupSchemeFullAEL2CuspidalCompactnessStatement : Prop :=
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
    let μG : Measure (AdelicGroupPoints F G) := Measure.haar
    ∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f μG),
      IsCompactOperator (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf)

end Langlands.Automorphic.GroupSchemeFunctions
