import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.RelativeIdentityComponent

/-! # Statement: centralizers of subgroups of multiplicative type over a general base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Centralizers of subgroups of multiplicative type** (Conrad, *Reductive group schemes*
(2014), Lemma 2.2.4 for subgroups of multiplicative type, and Remark 3.1.5). Let `G` be a
finitely presented affine group scheme over a scheme `S` and `i : H ⟶ G` a closed subgroup of
multiplicative type.
1. The centralizer functor `Z_G(H)` is represented by a finitely presented closed subgroup
   of `G`.
2. If `G` is smooth, every subgroup scheme representing `Z_G(H)` is smooth.
3. If `G` is reductive, then for every subgroup scheme `Z` representing `Z_G(H)` and every
   open subgroup `Z⁰` of `Z` representing its relative identity component, `Z⁰` is a
   reductive `S`-group, closed in `Z`, and every fibre `(Z_s)⁰ = Z⁰_s` is connected
   reductive. -/
def RelativeMultiplicativeTypeCentralizerStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] (H : CommGroupScheme S) (i : H.toGrp ⟶ G),
    IsMultiplicativeType H.toGrp → IsClosedSubgroup i →
      (∃ (Z : GroupScheme S) (z : Z ⟶ G),
        IsClosedSubgroup z ∧ LocallyOfFinitePresentation Z.X.hom ∧
          (torusCentralizer i).IsRepresentedBy z) ∧
      (Smooth G.X.hom → ∀ (Z : GroupScheme S) (z : Z ⟶ G),
        (torusCentralizer i).IsRepresentedBy z → Smooth Z.X.hom) ∧
      (IsReductive G → ∀ (Z : GroupScheme S) (z : Z ⟶ G),
        (torusCentralizer i).IsRepresentedBy z →
        ∀ (Z₀ : GroupScheme S) (z₀ : Z₀ ⟶ Z), IsRelativeIdentityComponent Z z₀ →
          IsReductive Z₀ ∧ IsClosedImmersion z₀.hom.hom.left ∧
            ∀ s : S, IsConnectedReductive (RelativeIdentityComponent.residueFiber Z₀ s))

end Langlands.GroupScheme
