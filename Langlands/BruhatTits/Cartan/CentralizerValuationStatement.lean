import Langlands.BruhatTits.Cartan.CentralizerValuation
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # The actual-centralizer character-restriction comparison -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.BruhatTits.Cartan

/-- For the represented algebraic centralizer of an actual maximal split torus,
restriction of rational characters followed by real evaluation is bijective.
This is a statement target, with neither building existence nor a Cartan
conclusion among its hypotheses. -/
def CentralizerValuationComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))), IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∀ (Z : GroupScheme (Spec (CommRingCat.of F))) (j : Z ⟶ G),
        IsClosedSubgroup j → (torusCentralizer i).IsRepresentedBy j →
        ∀ s : S.toGrp ⟶ Z, s ≫ j = i →
          Function.Bijective (restrictionEvaluation s)

end Langlands.BruhatTits.Cartan
