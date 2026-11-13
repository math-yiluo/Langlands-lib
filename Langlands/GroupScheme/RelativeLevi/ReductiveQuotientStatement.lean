import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: the quotient of a parabolic subgroup by its unipotent radical -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The reductive quotient of a parabolic subgroup** (Conrad, *Reductive group schemes*
(2014), Corollary 5.2.5, second paragraph). Let `S` be a scheme, `G` a reductive group
scheme over `S`, `i : P ⟶ G` a parabolic subgroup and `r : U ⟶ P` a unipotent radical of
`P`. Then the fppf quotient sheaf `P/U` is represented by a reductive group scheme `M`:
there is a homomorphism `q : P ⟶ M` that is flat, surjective and locally of finite
presentation and whose kernel is the image of `r` on every test scheme. Moreover every
homomorphism `f : P ⟶ H` onto a reductive group scheme `H` (surjective on underlying
schemes) factors as `q ≫ g` for exactly one homomorphism `g : M ⟶ H`. -/
def RelativeParabolicReductiveQuotientStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P U : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P),
    IsReductive G → IsRelativeParabolicSubgroup i → IsRelativeUnipotentRadical r →
      ∃ (M : GroupScheme S) (q : P ⟶ M),
        IsReductive M ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q ∧
        ∀ (H : GroupScheme S) (f : P ⟶ H), IsReductive H → Surjective f.hom.hom.left →
          ∃! g : M ⟶ H, q ≫ g = f

end Langlands.GroupScheme
