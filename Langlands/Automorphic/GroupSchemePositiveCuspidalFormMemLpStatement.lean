import Langlands.Automorphic.GroupSchemeCuspidalFormL2
import Langlands.Global.AdelicSplitCenterMeasure

/-! # Square integrability of descending classical cuspidal forms -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.PositiveRealTorus Langlands.GroupScheme

universe u

/-- Classical cuspidal forms descending to the positive rational quotient are
bounded and square integrable for its original Haar quotient measure. -/
def GroupSchemePositiveCuspidalFormMemLpStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    {d n : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (ρ : MatrixRepresentation G (Fin n)) (hρ : IsClosedSubgroup ρ) (hn : 0 < n)
    (K : Subgroup (InfiniteAdelicGroupPoints F G)) (hK : CompactIwasawa.IsMaximalCompact K)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (_hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (_e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (_hc : IsCentral i),
    ∀ f : C(PositiveRationalQuotient F G T i, ℂ),
      f ∈ positiveCuspidalFormSubrepresentation F G K ρ hsmooth hcalc hPD hG hρ hK hn T i →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B) ∧
        MemLp f 2 (positiveRationalQuotientHaarMeasure F G T i)

end Langlands.Automorphic.GroupSchemeFunctions
