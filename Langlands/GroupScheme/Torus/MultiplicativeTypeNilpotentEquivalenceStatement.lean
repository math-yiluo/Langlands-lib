import Langlands.GroupScheme.Torus.RelativeMultiplicativeType

/-! # Statement: multiplicative-type groups over a nilpotent thickening -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- Finite-type multiplicative-type groups lift along nilpotent thickenings, and reduction
is fully faithful on them (SGA 3, X, Proposition 2.1 and Corollary 4.5). The lifted object is
flat, as is every group of multiplicative type in the convention of Conrad B.1.1. -/
def MultiplicativeTypeNilpotentEquivalenceStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (J : Ideal A), IsNilpotent J →
    let r := Spec.algebraMap A (A ⧸ J)
    (∀ H₀ : GroupScheme (Spec (CommRingCat.of (A ⧸ J))), IsMultiplicativeType H₀ →
      ∃ H : GroupScheme (Spec (CommRingCat.of A)),
        IsMultiplicativeType H ∧ Flat H.X.hom ∧
          Nonempty ((GroupScheme.baseChange r).obj H ≅ H₀)) ∧
    (∀ H K : GroupScheme (Spec (CommRingCat.of A)),
      IsMultiplicativeType H → IsMultiplicativeType K →
        Function.Bijective (fun f : H ⟶ K => (GroupScheme.baseChange r).map f))

end Langlands.GroupScheme
