import Langlands.Global.InfinitePlaceIwasawaStatement
import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Archimedean Iwasawa existence adapted to an actual Levi subgroup -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.InfinitePlaceGroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Maximality among compact subgroups of the actual completion-point group. -/
def IsMaximalCompactSubgroup (v : NumberField.InfinitePlace F)
    (K : Subgroup (InfinitePlaceGroupPoints F G v)) : Prop :=
  IsCompact (K : Set (InfinitePlaceGroupPoints F G v)) ∧
    ∀ L : Subgroup (InfinitePlaceGroupPoints F G v),
      IsCompact (L : Set (InfinitePlaceGroupPoints F G v)) → K ≤ L → L = K

/-- Iwasawa coverage and the compact-intersection conclusions for a specified
parabolic and Levi, on the unchanged completion-valued point groups. -/
def IsLeviCompatibleIwasawaCompact
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)
    (v : NumberField.InfinitePlace F)
    (K : Subgroup (InfinitePlaceGroupPoints F G v)) : Prop :=
  IsMaximalCompactSubgroup F G v K ∧
    Set.range (P.affinePointsTarget p (CommAlgCat.of F v.Completion)) *
        (K : Set (InfinitePlaceGroupPoints F G v)) = Set.univ ∧
    Set.range (P.affinePointsTarget p (CommAlgCat.of F v.Completion)) ∩
        (K : Set (InfinitePlaceGroupPoints F G v)) =
      Set.range (M.affinePointsTarget (l ≫ p) (CommAlgCat.of F v.Completion)) ∩
        (K : Set (InfinitePlaceGroupPoints F G v)) ∧
    IsMaximalCompactSubgroup F M v
      (K.comap (M.affinePointsTarget (l ≫ p) (CommAlgCat.of F v.Completion)))

/-- For every actual rational parabolic and specified rational Levi, a maximal
compact subgroup exists with Iwasawa coverage and the Levi-intersection laws.
No compact subgroup, local comparison or decomposition is an input. -/
def LeviCompatibleIwasawaStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G),
      IsParabolicSubgroup p →
      ∀ (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P),
        IsRationalLeviSubgroup l →
        ∀ v : NumberField.InfinitePlace F,
          ∃ K : Subgroup (InfinitePlaceGroupPoints F G v),
            IsLeviCompatibleIwasawaCompact F G P p M l v K

/-- The compact part of the parabolic lies in the actual Levi image. -/
theorem IsLeviCompatibleIwasawaCompact.mem_levi
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
    {M : GroupScheme (Spec (CommRingCat.of F))} {l : M ⟶ P}
    {v : NumberField.InfinitePlace F}
    {K : Subgroup (InfinitePlaceGroupPoints F G v)}
    (hK : IsLeviCompatibleIwasawaCompact F G P p M l v K)
    {g : InfinitePlaceGroupPoints F G v}
    (hgP : g ∈ Set.range (P.affinePointsTarget p (CommAlgCat.of F v.Completion)))
    (hgK : g ∈ K) :
    g ∈ Set.range (M.affinePointsTarget (l ≫ p) (CommAlgCat.of F v.Completion)) := by
  have hg : g ∈ Set.range (P.affinePointsTarget p (CommAlgCat.of F v.Completion)) ∩
      (K : Set (InfinitePlaceGroupPoints F G v)) := ⟨hgP, hgK⟩
  rw [hK.2.2.1] at hg
  exact hg.1

end Langlands.Global.InfinitePlaceGroupPoints
