import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.GroupScheme.Absolute.Borel
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! # The adelic parabolic Iwasawa target -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Maximality among compact subgroups of the actual adelic point group. -/
def IsMaximalCompactSubgroup (K : Subgroup (AdelicGroupPoints F G)) : Prop :=
  IsCompact (K : Set (AdelicGroupPoints F G)) ∧
    ∀ K' : Subgroup (AdelicGroupPoints F G),
      IsCompact (K' : Set (AdelicGroupPoints F G)) → K ≤ K' → K' = K

/-- The actual parabolic image times a maximal compact subgroup covers the
ambient adelic group, with the parabolic factor on the left. -/
def IsParabolicIwasawaCompact
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (K : Subgroup (AdelicGroupPoints F G)) : Prop :=
  IsMaximalCompactSubgroup F G K ∧
    Set.range (map F P G p) * (K : Set (AdelicGroupPoints F G)) = Set.univ

/-- Getz–Hahn, Theorem 2.7.1, in the number-field case. This is an unproved
proposition target, with no supplied compact subgroup or coverage premise. -/
def ParabolicIwasawaStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))),
    Langlands.GroupScheme.IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G),
      Langlands.GroupScheme.IsParabolicSubgroup p →
      ∃ K : Subgroup (AdelicGroupPoints F G),
        IsParabolicIwasawaCompact F G P p K

end Langlands.Global.AdelicGroupPoints
