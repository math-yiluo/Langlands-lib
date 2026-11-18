import Langlands.AlgebraicGeometry.EtaleLocalSystem
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Statement: étale local systems over normal schemes are locally isotrivial -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open EtaleLocalSystem in
/-- **Local isotriviality of étale local systems over normal bases** (Conrad, *Reductive group
schemes* (2014), proof of Corollary B.3.6, first paragraph). Let `S` be a normal scheme (every
local ring is an integrally closed domain) and `F` a locally constant abelian sheaf with finitely
generated coefficients on the big étale site of `S`.
1. Zariski-locally on `S`, `F` is isotrivial: every point of `S` has an open neighbourhood `U`
   with a finite étale surjective `p : U' ⟶ U` such that the restriction of `F` to `U'` is the
   constant sheaf of a finitely generated abelian group.
2. If `S` is irreducible, `F` is isotrivial: its restriction along some finite étale surjective
   `p : S' ⟶ S` is the constant sheaf of a finitely generated abelian group. -/
def EtaleLocalSystemNormalIsotrivialStatement : Prop :=
  ∀ (S : Scheme.{u}),
    (∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)) →
    ∀ F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}, IsFinitelyGeneratedLocallyConstant.{u, u} F →
      (∀ s : S, ∃ U : S.Opens, s ∈ U ∧
        ∃ (U' : Scheme.{u}) (p : U' ⟶ U.toScheme), IsFinite p ∧ Etale p ∧ Surjective p ∧
          ∃ M : AddCommGrpCat.{u}, AddGroup.FG M ∧
            Nonempty (restrict (p ≫ U.ι) F ≅ constant U' M)) ∧
      (IrreducibleSpace S →
        ∃ (S' : Scheme.{u}) (p : S' ⟶ S), IsFinite p ∧ Etale p ∧ Surjective p ∧
          ∃ M : AddCommGrpCat.{u}, AddGroup.FG M ∧ Nonempty (restrict p F ≅ constant S' M))

end Langlands.AlgebraicGeometry
