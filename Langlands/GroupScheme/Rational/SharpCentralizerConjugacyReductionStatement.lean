import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.SubgroupConjugacy
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # Actual-image conjugacy of represented centralizers: reduction statement -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An actual rational product removes a centralizer factor from an ordinary
conjugator. This proposition retains the product and ordinary conjugacy as inputs. -/
def SharpCentralizerConjugacyReductionStatement : Prop :=
  ∀ {k : Type u} [Field k]
    {G C Z Z' : GroupScheme (Spec (CommRingCat.of k))}
    {A A' : CommGroupScheme (Spec (CommRingCat.of k))}
    (a : A.toGrp ⟶ G) (a' : A'.toGrp ⟶ G)
    (j : Z ⟶ G) (j' : Z' ⟶ G) (p : C ⟶ G),
    (torusCentralizer a).IsRepresentedBy j →
    (torusCentralizer a').IsRepresentedBy j' →
    SubgroupConjugate a a' →
    (∀ g : rationalPoints G,
      ∃ c : rationalPoints C, ∃ z : rationalPoints Z,
        g = rationalPoints.map p c * rationalPoints.map j z) →
    ∃ g ∈ (rationalPoints.map p).range, ∃ e : Z ≅ Z',
      j ≫ (G.innerIso g).hom = e.hom ≫ j'

end Langlands.GroupScheme
