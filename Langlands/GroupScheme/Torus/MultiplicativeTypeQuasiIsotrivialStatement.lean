import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Henselian

/-! # Statement: groups of multiplicative type split étale-locally -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Groups of multiplicative type are quasi-isotrivial** (Conrad, *Reductive group schemes*
(2014), Proposition B.3.4, first and last assertions).
1. A group `H` over a scheme `S` that becomes diagonalizable on an fppf cover of `S` already
   becomes diagonalizable on an étale cover of `S`.
2. If `S = Spec A` for a henselian local ring `A`, then `H` becomes diagonalizable after base
   change along a finite étale surjective morphism `S' → S`. -/
def MultiplicativeTypeQuasiIsotrivialStatement : Prop :=
  (∀ (S : Scheme.{u}) (H : GroupScheme S), IsMultiplicativeType H →
    ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ i : 𝒰.I₀, IsDiagonalizable ((GroupScheme.baseChange (𝒰.f i)).obj H)) ∧
  (∀ (A : Type u) [CommRing A] [HenselianLocalRing A]
    (H : GroupScheme (Spec (CommRingCat.of A))), IsMultiplicativeType H →
    ∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of A)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        IsDiagonalizable ((GroupScheme.baseChange p).obj H))

end Langlands.GroupScheme
