import Langlands.Sheaf.Renard.SingletonSheaves
import Langlands.Topology.LocallyProfinite
import Mathlib.CategoryTheory.Equivalence

/-!
# Renard III.3.2: the singleton category identification

The target refers to the published original-section unit and literal
coefficient-evaluation counit, and to the actual two singleton functors.
-/

namespace Langlands.Sheaf.Renard.SingletonEquivalence

open CategoryTheory
open Langlands.Sheaf.Renard.SectionActions

universe uG

/-- The singleton identification is an equivalence with the exact existing unit,
counit and both triangle laws, retaining all original sections and maps. -/
def Statement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    Langlands.Topology.IsLocallyProfinite G →
      IsIso (SingletonSheaves.unit G) ∧
      IsIso (SingletonSheaves.counit G) ∧
      (∀ F : SmoothActionSheaf G PUnit,
        (gammaC G PUnit).map ((SingletonSheaves.unit G).app F) ≫
            (SingletonSheaves.counit G).app ((gammaC G PUnit).obj F) =
          𝟙 ((gammaC G PUnit).obj F)) ∧
      (∀ A : Langlands.SmoothRep.{0, uG, 0} ℂ G,
        (SingletonSheaves.unit G).app ((SingletonSheaves.functor G).obj A) ≫
            (SingletonSheaves.functor G).map ((SingletonSheaves.counit G).app A) =
          𝟙 ((SingletonSheaves.functor G).obj A)) ∧
      (gammaC G PUnit).IsEquivalence ∧ (SingletonSheaves.functor G).IsEquivalence

end Langlands.Sheaf.Renard.SingletonEquivalence
