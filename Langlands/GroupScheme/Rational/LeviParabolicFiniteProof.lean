import Langlands.GroupScheme.Rational.LeviSplitComponentRecallStatements
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.SplitComponentProof

/-! # Finitely many rational parabolics share an embedded rational Levi (Renard V.3.1)

Every parabolic with the embedded Levi `M` is the dynamic parabolic of a cocharacter of the
split component `A_M`. Pushed into one maximal split torus `T₀`, such a cocharacter is
determined, as far as its dynamic parabolic goes, by the set of relative roots of `T₀` on
which it is nonnegative. The finite set of relative roots of `T₀` thus bounds the family by
`2 ^ |Φ(T₀)|`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Renard V.3.1: the set `P(M)` of rational parabolics with a fixed embedded rational Levi
`M` is finite, in the form of a uniform bound `2 ^ |Φ(T₀)|` on families with distinct
images, where `Φ(T₀)` is the finite set of relative roots of one maximal split torus. -/
theorem leviParabolicFinite : LeviParabolicFiniteStatement.{u} := by
  classical
  intro k _ G hG P M p l hp hl
  let := hG.isAffineHom
  let := hG.smooth
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hl.isConnectedReductive).1
  obtain ⟨R⟩ := parabolicRootPresentationExistence k G hG P M A p l a hp hl ha
  have hfin :=
    R.isCompatible.maximalSplit.isSplitSubtorus.1.finite_relativeRoots R.data.i
  let roots : Finset (characterLattice R.data.T) := hfin.toFinset
  refine ⟨2 ^ roots.card, ?_⟩
  intro n Q q lQ hq hlQ hcomp hinj
  let S (i : Fin n) : ParabolicRootPresentation (q i) (lQ i) a :=
    Classical.choice (parabolicRootPresentationExistence k G hG (Q i) M A
      (q i) (lQ i) a (hq i) (hlQ i) ha)
  let ζ (i : Fin n) : cocharacterLattice R.data.T :=
    RealTorusSpace.cocharacterMapInt R.data.f (S i).splitComponentCocharacter
  have hζ (i : Fin n) : CommGroupScheme.groupHom (ζ i) ≫ R.data.i =
      CommGroupScheme.groupHom (S i).splitComponentCocharacter ≫ a ≫ lQ i ≫ q i := by
    change (CommGroupScheme.groupHom (S i).splitComponentCocharacter ≫
      CommGroupScheme.groupHom R.data.f) ≫ R.data.i = _
    rw [Category.assoc, R.isCompatible.factor_comp, hcomp i]
  have hrange (i : Fin n) : SubgroupFunctor.range (q i) =
      Dynamic.parabolic (CommGroupScheme.groupHom (ζ i) ≫ R.data.i) := by
    rw [hζ i]
    exact (S i).parabolic_eq_splitComponentCocharacter
  let sign (i : Fin n) : Finset (characterLattice R.data.T) :=
    roots.filter fun α => 0 ≤ latticePairing R.data.T α (ζ i)
  have hsign : Set.InjOn sign (Finset.univ : Finset (Fin n)) := by
    intro i _ j _ he
    have hiff : ∀ α ∈ relativeRoots R.data.i,
        (0 ≤ latticePairing R.data.T α (ζ i) ↔ 0 ≤ latticePairing R.data.T α (ζ j)) := by
      intro α hα
      have hmem : α ∈ roots := hfin.mem_toFinset.mpr hα
      constructor
      · intro h
        have hi : α ∈ sign i := Finset.mem_filter.mpr ⟨hmem, h⟩
        rw [he] at hi
        exact (Finset.mem_filter.mp hi).2
      · intro h
        have hj : α ∈ sign j := Finset.mem_filter.mpr ⟨hmem, h⟩
        rw [← he] at hj
        exact (Finset.mem_filter.mp hj).2
    have hij := (relativeRootSignInclusions k G hG R.data.T R.data.i
      R.isCompatible.maximalSplit (ζ i) (ζ j)).1
    have hji := (relativeRootSignInclusions k G hG R.data.T R.data.i
      R.isCompatible.maximalSplit (ζ j) (ζ i)).1
    apply hinj
    change SubgroupFunctor.range (q i) = SubgroupFunctor.range (q j)
    rw [hrange i, hrange j]
    exact le_antisymm (hij.mpr fun α hα h => (hiff α hα).mp h)
      (hji.mpr fun α hα h => (hiff α hα).mpr h)
  have hmaps : Set.MapsTo sign (Finset.univ : Finset (Fin n)) roots.powerset := by
    intro i _
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hcard := Finset.card_le_card_of_injOn sign hmaps hsign
  simpa only [Finset.card_univ, Fintype.card_fin, Finset.card_powerset] using hcard

end Langlands.GroupScheme
