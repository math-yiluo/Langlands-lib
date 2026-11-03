import Langlands.GroupScheme.Adjoint.SplitTorus

/-! # Existence statement for the image of a maximal split torus in an adjoint quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field, every actual maximal split torus of a connected reductive group has
an actual maximal split image torus in every actual adjoint quotient, reached by an fppf
torus homomorphism completing the actual commutative square. -/
def AdjointSplitTorusImageExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G A : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ A) (i : T.toGrp ⟶ G),
    IsAdjointQuotient q → IsMaximalSplitTorus i →
      ∃ (T_ad : CommGroupScheme (Spec (CommRingCat.of k))) (j : T_ad.toGrp ⟶ A)
        (p : T ⟶ T_ad), IsAdjointSplitTorusImage q i j p

end Langlands.GroupScheme
