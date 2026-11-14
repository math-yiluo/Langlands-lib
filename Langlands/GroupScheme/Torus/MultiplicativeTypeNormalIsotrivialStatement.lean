import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Statement: groups of multiplicative type over normal bases are locally isotrivial -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Local isotriviality over normal bases** (Conrad, *Reductive group schemes* (2014),
Corollary B.3.6, first two sentences). Let `S` be a normal scheme (every local ring is an
integrally closed domain) and `H` a group of multiplicative type over `S`.
1. `H` is locally isotrivial: every point of `S` has an open neighbourhood `U` such that
   `H_U` becomes diagonalizable after base change along a finite étale surjective morphism
   `U' → U`.
2. If `S` is irreducible, `H` is isotrivial: it becomes diagonalizable after base change
   along a finite étale surjective morphism `S' → S`. -/
def MultiplicativeTypeNormalIsotrivialStatement : Prop :=
  ∀ (S : Scheme.{u}),
    (∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)) →
    ∀ H : GroupScheme S, IsMultiplicativeType H →
      (∀ s : S, ∃ U : S.Opens, s ∈ U ∧
        ∃ (U' : Scheme.{u}) (p : U' ⟶ U.toScheme), IsFinite p ∧ Etale p ∧ Surjective p ∧
          IsDiagonalizable ((GroupScheme.baseChange (p ≫ U.ι)).obj H)) ∧
      (IrreducibleSpace S →
        ∃ (S' : Scheme.{u}) (p : S' ⟶ S), IsFinite p ∧ Etale p ∧ Surjective p ∧
          IsDiagonalizable ((GroupScheme.baseChange p).obj H))

end Langlands.GroupScheme
