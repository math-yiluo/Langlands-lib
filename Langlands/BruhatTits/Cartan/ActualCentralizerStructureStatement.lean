import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # The reductive centralizer and its actual split component -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.BruhatTits.Cartan

/-- The represented algebraic centralizer of a maximal split torus is connected
reductive, and the actual factorization of that torus is its split component.
These are conclusions, rather than supplied structural certificates. -/
def ActualCentralizerStructureStatement : Prop :=
  ∀ (F : Type u) [Field F]
    (G : GroupScheme (Spec (CommRingCat.of F))), IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∀ (Z : GroupScheme (Spec (CommRingCat.of F))) (j : Z ⟶ G),
        IsClosedSubgroup j → (torusCentralizer i).IsRepresentedBy j →
        ∀ s : S.toGrp ⟶ Z, s ≫ j = i →
          IsConnectedReductive Z ∧ IsSplitComponent s

end Langlands.BruhatTits.Cartan
