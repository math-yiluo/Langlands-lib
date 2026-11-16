import Langlands.GroupScheme.Adjoint.RelativeExistenceStatement
import Langlands.GroupScheme.Reductive.RelativeCenterStatement

/-! # Affine quotients by central subgroups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth affine group with connected geometric fibres over any scheme has
an affine fppf quotient by every closed central subgroup of multiplicative type.
This isolates the quotient construction used in Conrad, Lemma 3.3.2. -/
def RelativeCentralMultiplicativeTypeQuotientStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S),
    Smooth G.X.hom → IsAffineHom G.X.hom →
    (∀ s : S, ConnectedSpace (geometricFiber G s).X.left) →
    ∀ (Z : GroupScheme S) (z : Z ⟶ G),
      IsClosedSubgroup z → IsCentral z →
      RelativeMultiplicativeType.IsMultiplicativeType Z →
      ∃ (Q : GroupScheme S) (q : G ⟶ Q),
        IsAffineHom Q.X.hom ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q

/-- The full-centre quotient target follows from the relative centre theorem
and the central multiplicative-type quotient construction. -/
theorem relativeAdjointQuotientExistence_of_center_and_centralMultiplicativeTypeQuotients
    (hcenter : ReductiveRelativeCenterStatement.{u})
    (hquotient : RelativeCentralMultiplicativeTypeQuotientStatement.{u}) :
    RelativeAdjointQuotientExistenceStatement.{u} := by
  intro S G hG
  obtain ⟨Z, z, hz, hZ, _⟩ := hcenter S G hG
  obtain ⟨Q, q, hQ, hq⟩ :=
    hquotient S G hG.smooth hG.isAffineHom
      (fun s => (hG.geometricFiber s).connectedSpace) Z z hz.1 hz.isCentral hZ
  refine ⟨Q, q, hQ, ?_⟩
  simpa only [hz.2] using hq

end Langlands.GroupScheme
