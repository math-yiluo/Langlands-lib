import Langlands.GroupScheme.Reductive.Basic

/-! # Affineness of a represented quotient of an affine algebraic group -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A faithfully flat, quasi-compact quotient homomorphism from an affine
finite-type group over a field has affine target. The target is an actual
separated finite-type group scheme, with no affineness premise. -/
def AffineGroupSchemeQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G Q : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType Q.X.hom] [QuasiCompact Q.X.hom] [IsSeparated Q.X.hom]
    (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] [QuasiCompact q.hom.hom.left],
      IsAffineHom Q.X.hom

end Langlands.GroupScheme
