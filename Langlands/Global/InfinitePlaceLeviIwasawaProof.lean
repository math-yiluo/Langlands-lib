import Langlands.Global.InfinitePlaceLeviIwasawaStatement
import Langlands.Global.InfinitePlaceLeviIwasawaDynamic
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # Actual archimedean Iwasawa existence compatible with a rational Levi: proof -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.InfinitePlaceGroupPoints

open Langlands.GroupScheme

/-- Existence at one place: for a connected reductive group, a parabolic
subgroup and a specified rational Levi subgroup, the actual completion-point
group has a compact subgroup satisfying all four Levi-compatible Iwasawa
conclusions. -/
theorem exists_leviCompatibleIwasawaCompact
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p)
    (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)
    (hl : IsRationalLeviSubgroup l) (v : NumberField.InfinitePlace F) :
    ∃ K : Subgroup (InfinitePlaceGroupPoints F G v),
      IsLeviCompatibleIwasawaCompact F G P p M l v K :=
  exists_leviCompatibleIwasawaCompact_of_dynamic parabolicDynamic
    dynamicGeometricUnipotentRadical F G hG P p hp M l hl v

/-- **Actual archimedean Iwasawa existence compatible with a specified rational
Levi.** For every number field, connected reductive group, parabolic subgroup,
rational Levi subgroup of it and infinite place, the actual completion-point
group has a maximal compact subgroup with parabolic Iwasawa coverage, equal
parabolic and Levi intersections, and maximal compact inverse image in the
Levi point group. -/
theorem leviCompatibleIwasawaStatement : LeviCompatibleIwasawaStatement.{u} := by
  intro F _ _ G hG P p hp M l hl v
  exact exists_leviCompatibleIwasawaCompact F G hG P p hp M l hl v

end Langlands.Global.InfinitePlaceGroupPoints
