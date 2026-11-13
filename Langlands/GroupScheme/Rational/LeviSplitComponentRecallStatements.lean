import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Reductive.Basic

/-!
# Levi subgroups, split components and `P(M)` (Renard V.3.1 and V.3.5, recalled)

For a rational Levi `M` of a rational parabolic of a connected reductive group with split
component `A_M`: `Z_G(A_M) = M`; `N_G(A_M) = N_G(M)` on rational points; and the set `P(M)`
of rational parabolics with Levi factor `M` is finite.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Renard V.3.1 and (V.3.5.1), recalled from Borel–Tits: for a rational Levi `l : L ⟶ P` of a
rational parabolic `j : P ⟶ G` of a connected reductive group, and a split component
`a : A ⟶ L` of `L`, the centralizer of `A_M` in `G` is `M`:
`Z_G(A_M) = M` as subgroup functors. -/
def LeviSplitComponentCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P L : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G) (l : L ⟶ P),
      IsParabolicSubgroup j → IsRationalLeviSubgroup l →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ L),
        IsSplitComponent a →
        torusCentralizer (a ≫ l ≫ j) = SubgroupFunctor.range (l ≫ j)

/-- Renard (V.3.5.1), recalled: with the data of `LeviSplitComponentCentralizerStatement`, a
rational point of `G` normalizes `A_M` if and only if it normalizes `M`:
`N_G(A_M) = N_G(M)` in `G = G(F)`. -/
def LeviSplitComponentNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P L : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G) (l : L ⟶ P),
      IsParabolicSubgroup j → IsRationalLeviSubgroup l →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ L),
        IsSplitComponent a →
        (torusNormalizer (a ≫ l ≫ j)).carrier (Over.mk (𝟙 _)) =
          (SubgroupFunctor.range (l ≫ j)).normalizer.carrier (Over.mk (𝟙 _))

/-- Renard V.3.1, recalled: for a rational Levi `M` of a rational parabolic, the set `P(M)` of
rational parabolics admitting `M` as a Levi factor is finite. Finiteness is stated as a bound
on the length of every finite family of rational parabolics `q i : Q i ⟶ G` with pairwise
distinct images, each having the embedded `M` as a rational Levi factor. -/
def LeviParabolicFiniteStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P M : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l →
      ∃ N : ℕ, ∀ (n : ℕ) (Q : Fin n → GroupScheme (Spec (CommRingCat.of k)))
        (q : ∀ i, Q i ⟶ G) (lQ : ∀ i, M ⟶ Q i),
        (∀ i, IsParabolicSubgroup (q i)) →
        (∀ i, IsRationalLeviSubgroup (lQ i)) →
        (∀ i, lQ i ≫ q i = l ≫ p) →
        Function.Injective (fun i => SubgroupFunctor.range (q i)) → n ≤ N

/-- The three recalled assertions above. -/
def LeviSplitComponentRecallStatements : Prop :=
  LeviSplitComponentCentralizerStatement.{u} ∧ LeviSplitComponentNormalizerStatement.{u} ∧
    LeviParabolicFiniteStatement.{u}

end Langlands.GroupScheme
