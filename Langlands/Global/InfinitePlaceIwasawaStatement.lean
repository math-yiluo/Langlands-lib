import Langlands.Global.InfiniteAdelicGroupProduct
import Langlands.GroupScheme.Absolute.Borel
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! # Actual archimedean local parabolic Iwasawa existence -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.InfinitePlaceGroupPoints

/-- The archimedean local existence target on the actual completion-point group.
The compact subgroup is a conclusion; no decomposition or comparison is assumed. -/
def ParabolicIwasawaStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))),
    Langlands.GroupScheme.IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G),
      Langlands.GroupScheme.IsParabolicSubgroup p →
      ∀ v : NumberField.InfinitePlace F,
        ∃ K : Subgroup (InfinitePlaceGroupPoints F G v),
          IsCompact (K : Set (InfinitePlaceGroupPoints F G v)) ∧
          (∀ L : Subgroup (InfinitePlaceGroupPoints F G v),
            IsCompact (L : Set (InfinitePlaceGroupPoints F G v)) → K ≤ L → L = K) ∧
          Set.range (P.affinePointsTarget p (CommAlgCat.of F v.Completion)) *
            (K : Set (InfinitePlaceGroupPoints F G v)) = Set.univ

end Langlands.Global.InfinitePlaceGroupPoints
