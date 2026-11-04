import Langlands.GroupScheme.Nilpotent.CentralTorusStatement
import Langlands.GroupScheme.Torus.FiniteFieldGeometricMaximalStatement
import Langlands.GroupScheme.Torus.AlgClosedTrivialMaximalUnipotentStatement

/-! # Statement: the nilpotent and finite-field no-torus reductions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The nilpotent and finite-field cases reduce to their explicit structural
inputs. Neither implication assumes the arbitrary-field no-torus theorem. -/
def NoTorusBasicReductionStatement : Prop :=
  (NilpotentCentralTorusStatement.{u} →
    ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
      IsNilpotentGroupScheme G →
      (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
        ∀ g : T.toGrp ⟶ G, SubgroupFunctor.range g = ⊥) →
      IsUnipotent G) ∧
  (FiniteFieldGeometricMaximalTorusStatement.{u} →
    AlgClosedTrivialMaximalTorusUnipotentStatement.{u} →
    ∀ (k : Type u) [Field k] [Finite k]
      (G : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
      (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
        ∀ g : T.toGrp ⟶ G, SubgroupFunctor.range g = ⊥) →
      IsUnipotent G)

end Langlands.GroupScheme
