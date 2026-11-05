import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerStatement
import Langlands.GroupScheme.Rational.ConjugacyStatement
import Langlands.GroupScheme.Rational.TorusCentralizerConjugacy
import Langlands.GroupScheme.Rational.TorusCentralizerTorusComparison

/-! # Reduction to one maximal split torus with a torus centralizer -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every quasi-split field group has some maximal split torus whose whole-group
centralizer is represented by a closed torus. This is an explicit geometric
existence statement, not a proved existence theorem. -/
def QuasiSplitTorusCentralizerExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsQuasiSplit G →
      ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G)
        (C : GroupScheme (Spec (CommRingCat.of k))) (j : C ⟶ G),
        IsMaximalSplitTorus a ∧ (torusCentralizer a).IsRepresentedBy j ∧
          IsClosedSubgroup j ∧ IsTorus C

/-- Existence for one maximal split torus, together with ordinary maximal split
torus conjugacy, implies the exact supplied-maximal-torus centralizer statement.
Both structural inputs remain explicit premises. -/
theorem quasiSplitMaximalTorusCentralizer_of_exists_torusCentralizer
    (hex : QuasiSplitTorusCentralizerExistenceStatement.{u})
    (hconj : MaximalSplitTorusConjugacyStatement.{u}) :
    QuasiSplitMaximalTorusCentralizerStatement.{u} := by
  intro k _ G hG T A i a f hi ha hf
  obtain ⟨A₀, a₀, C, j₀, ha₀, hj₀, hj₀c, hC⟩ := hex k G hG
  obtain ⟨g, e, he⟩ :=
    (hconj k G hG.isConnectedReductive).1 A₀ A a₀ a ha₀ ha
  have hj := hj₀.torusCentralizer_of_iso_square e (G.innerIso g) he
  exact hi.isRepresentedBy_torusCentralizer_of_isTorus f hf
    (j₀ ≫ (G.innerIso g).hom) hj (hj₀c.comp_iso (G.innerIso g)) hC

end Langlands.GroupScheme
