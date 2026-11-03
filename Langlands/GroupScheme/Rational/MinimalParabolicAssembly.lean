import Langlands.GroupScheme.Rational.MinimalParabolicStatement
import Langlands.GroupScheme.Rational.ParabolicTorusStatement
import Langlands.GroupScheme.Rational.SplitRankReduction

/-! # Conditional assembly of maximal split-torus conjugacy -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every maximal split torus of a connected reductive group factors through a minimal
parabolic subgroup. This geometric assertion is a premise of the reductions below. -/
def MaximalSplitTorusMinimalParabolicContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i →
        ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
          IsMinimalParabolicSubgroup j ∧ ∃ f : T.toGrp ⟶ P, f ≫ j = i

/-- The minimal-parabolic route to rational conjugacy, with all geometric inputs explicit. -/
theorem maximalSplitTorus_subgroupConjugate_of_minimalParabolics
    (hParabolic : MinimalParabolicConjugacyStatement.{u})
    (hInside : MinimalParabolicSplitTorusConjugacyStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (hContains : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i →
        ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
          IsMinimalParabolicSubgroup j ∧ ∃ f : T.toGrp ⟶ P, f ≫ j = i)
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (i' : T'.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i') :
    SubgroupConjugate i i' := by
  obtain ⟨P, j, hj, f, hf⟩ := hContains T i hi
  obtain ⟨P', j', hj', f', hf'⟩ := hContains T' i' hi'
  obtain ⟨g, e, he⟩ := hParabolic k G hG P P' j j' hj hj'
  have hTransport : (f ≫ e.hom) ≫ j' = i ≫ (G.innerIso g).hom := by
    rw [Category.assoc, ← he, ← Category.assoc, hf]
  have hiTransport : IsMaximalSplitTorus (i ≫ (G.innerIso g).hom) :=
    hi.comp_iso (G.innerIso g)
  have hInside' : SubgroupConjugate (f ≫ e.hom) f' :=
    hInside k G hG P' j' hj' T T' (i ≫ (G.innerIso g).hom) i'
      hiTransport hi' (f ≫ e.hom) f' hTransport hf'
  simpa only [hf, hf'] using
    SubgroupConjugate.of_overgroups j j' f f' g e he hInside'

/-- Combining the explicit minimal-parabolic inputs and maximal extension gives both
clauses of the existing statement. No input is asserted unconditionally here. -/
theorem maximalSplitTorusConjugacyStatement_of_minimalParabolics_extension
    (hParabolic : MinimalParabolicConjugacyStatement.{u})
    (hInside : MinimalParabolicSplitTorusConjugacyStatement.{u})
    (hContains : MaximalSplitTorusMinimalParabolicContainmentStatement.{u})
    (hExtension : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G →
      ∀ (J : Type u) [Finite J] (j : splitTorus (Spec (CommRingCat.of k)) J ⟶ G),
        IsClosedSubgroup j →
          ∃ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G),
            IsMaximalSplitTorus i' ∧
              ∃ f : splitTorus (Spec (CommRingCat.of k)) J ⟶ T'.toGrp, f ≫ i' = j) :
    MaximalSplitTorusConjugacyStatement.{u} := by
  apply maximalSplitTorusConjugacyStatement_of_extension_conjugacy hExtension
  intro k _ G hG
  exact maximalSplitTorus_subgroupConjugate_of_minimalParabolics
    hParabolic hInside hG (hContains k G hG)

end Langlands.GroupScheme
