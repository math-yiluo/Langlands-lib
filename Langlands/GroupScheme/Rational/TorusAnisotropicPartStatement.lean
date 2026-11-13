import Langlands.GroupScheme.Rational.TorusSplitPart
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.LeviSubgroup

/-!
# The anisotropic part of a torus (Renard V.2.2, Remark 2, recalled)

Every torus `T` over a field has a unique maximal anisotropic subtorus `T_an`, and `T` is the
almost direct product of its largest split subtorus `A` and `T_an`: the multiplication
`A × T_an → T` is surjective and finite.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Renard V.2.2, Remark 2, recalled: a torus `T` over a field `k` has a closed anisotropic
subtorus `b : T_an ⟶ T` through which every closed anisotropic subtorus of `T` factors (the
unique maximal anisotropic subtorus), and for every largest split subtorus `a : A ⟶ T` the
multiplication morphism `A × T_an → T` is surjective and finite: `A` and `T_an` generate `T`
and their intersection is finite. -/
def TorusAnisotropicPartStatement : Prop :=
  ∀ (k : Type u) [Field k] (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsTorus T.toGrp →
    ∃ (B : CommGroupScheme (Spec (CommRingCat.of k))) (b : B.toGrp ⟶ T.toGrp),
      IsClosedSubgroup b ∧ IsTorus B.toGrp ∧ IsAnisotropic B.toGrp ∧
      (∀ (C : CommGroupScheme (Spec (CommRingCat.of k))) (c : C.toGrp ⟶ T.toGrp),
        IsClosedSubgroup c → IsTorus C.toGrp → IsAnisotropic C.toGrp →
          ∃ f : C.toGrp ⟶ B.toGrp, f ≫ b = c) ∧
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ T.toGrp),
        IsLargestSplitSubtorus a →
          Surjective (subgroupMultiplication a b).left ∧
            IsFinite (subgroupMultiplication a b).left

end Langlands.GroupScheme
