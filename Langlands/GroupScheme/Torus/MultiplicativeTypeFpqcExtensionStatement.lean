import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: fpqc descent and extensions for groups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **fpqc descent and extensions of groups of multiplicative type** (Conrad, *Reductive group
schemes* (2014), Corollary B.4.2). Let `S` be a scheme.
1. An `S`-affine fppf `S`-group `H` that becomes of multiplicative type after base change along
   a flat, surjective, quasi-compact morphism `S' ⟶ S` is of multiplicative type.
2. Let `1 → H' → H → H'' → 1` be a short exact sequence of `S`-affine fppf `S`-groups: `i` is a
   monomorphism and `q` is an fppf quotient map with kernel `i(H')`. If `H'` and `H''` are of
   multiplicative type and every fibre `H_s` is connected or commutative, then `H` is of
   multiplicative type. -/
def MultiplicativeTypeFpqcExtensionStatement : Prop :=
  ∀ S : Scheme.{u},
    (∀ (H : GroupScheme S) [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
      [IsAffineHom H.X.hom] (S' : Scheme.{u}) (b : S' ⟶ S) [Flat b] [Surjective b]
      [QuasiCompact b],
      RelativeMultiplicativeType.IsMultiplicativeType ((GroupScheme.baseChange b).obj H) →
        RelativeMultiplicativeType.IsMultiplicativeType H) ∧
    (∀ (H' H H'' : GroupScheme S)
      [Flat H'.X.hom] [LocallyOfFinitePresentation H'.X.hom] [IsAffineHom H'.X.hom]
      [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom] [IsAffineHom H.X.hom]
      [Flat H''.X.hom] [LocallyOfFinitePresentation H''.X.hom] [IsAffineHom H''.X.hom]
      (i : H' ⟶ H) (q : H ⟶ H''),
      Mono i.hom.hom → RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q →
        RelativeMultiplicativeType.IsMultiplicativeType H' →
        RelativeMultiplicativeType.IsMultiplicativeType H'' →
        (∀ s : S, ConnectedSpace (RelativeIdentityComponent.residueFiber H s).X.left ∨
          IsCommMonObj (RelativeIdentityComponent.residueFiber H s).X) →
        RelativeMultiplicativeType.IsMultiplicativeType H)

end Langlands.GroupScheme
