import Langlands.Global.AdelicGroupLocalPoints
import Langlands.Global.CoordinateCompactPatching
import Langlands.GroupScheme.Absolute.Borel

/-! # Actual finite-place parabolic Iwasawa existence -/

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.FinitePlaceGroupPoints

/-- The finite-place existence input for actual adelic Iwasawa assembly.
The compact subgroup is a conclusion, with unrestricted compact maximality. -/
def ParabolicIwasawaStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))),
    Langlands.GroupScheme.IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G),
      Langlands.GroupScheme.IsParabolicSubgroup p →
      ∀ v : FinitePlace F, ∃ K : Subgroup (FinitePlaceGroupPoints F G v),
        CoordinateCompactPatching.IsLocalIwasawaCompact
          (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))) K

end Langlands.Global.FinitePlaceGroupPoints
