import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # Maximally split maximal tori as whole-torus centralizers in quasi-split groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- In a quasi-split connected reductive group, any maximal torus containing
an ambient maximal split torus represents its whole-group centralizer. -/
def QuasiSplitMaximalTorusCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsQuasiSplit G →
    ∀ (T A : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ G) (a : A.toGrp ⟶ G) (f : A.toGrp ⟶ T.toGrp),
      IsMaximalTorus i → IsMaximalSplitTorus a → f ≫ i = a →
        (torusCentralizer a).IsRepresentedBy i

end Langlands.GroupScheme
