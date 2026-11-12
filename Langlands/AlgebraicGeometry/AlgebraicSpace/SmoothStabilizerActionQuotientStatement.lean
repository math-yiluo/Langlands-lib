import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitQuotientStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-!
# Quotients by smooth group actions with smooth stabilizers

The smooth case of the quotient of a scheme by a group action with flat stabilizer, after
the Stacks Project's proof of Proposition 101.28.9 (Tag 06QJ), which forms the quotient
`R' = R/G` of the arrow space by the stabilizer with Bootstrap Lemma 80.11.7 (Tag 06PH),
and then the quotient of the scheme by the equivalence relation `R'` with Bootstrap
Theorem 80.10.1 (Tag 04S6). Let a smooth group scheme `G` over `S` act on a scheme `V`
locally of finite type over `S`, with stabilizer scheme smooth over `V`. Then the fppf
sheaf quotient of `V` by `G` exists as an algebraic space, and for every such quotient
the quotient map is smooth and surjective and the quotient is locally of finite type
over `S`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Quotients by smooth group actions with smooth stabilizers: let `G` be a group scheme
smooth over a scheme `S`, acting by `a` on a scheme `V` locally of finite type over `S`,
such that the stabilizer scheme, the base change of the action graph `(g, v) ↦ (g.v, v)`
along the diagonal of `V`, is smooth over `V`. Then there are an algebraic space `X` over
`S` and an fppf quotient map `π : V ⟶ X` of the action, and for every algebraic space `X`
with an fppf quotient map `π : V ⟶ X`, the map `π` is smooth and surjective and `X` is
locally of finite type over `S`. -/
def SmoothStabilizerActionQuotientStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) (V : Over S) (a : SchemeAction G V),
    Smooth G.X.hom → LocallyOfFiniteType V.hom →
    Smooth (pullback.snd (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))).left →
      (∃ (X : AlgebraicSpace S) (π : (schemeSheaf S).obj V ⟶ X.toSheaf),
          IsFppfActionQuotient a π) ∧
        ∀ (X : AlgebraicSpace S) (π : (schemeSheaf S).obj V ⟶ X.toSheaf),
          IsFppfActionQuotient a π →
            IsSmooth π.hom ∧ IsSurjective π.hom ∧ LocallyOfFiniteTypeOverBase X

end Langlands.AlgebraicGeometry.AlgebraicSpace
