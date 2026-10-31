import Langlands.AbelianScheme.InversionCriterion
import Langlands.AbelianScheme.PointedMorphismRigidityProof

/-! # Equivalence of the geometric and bundled abelian-scheme definitions -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

/-- Every geometrically abelian group scheme admits the bundle with exactly its
original group object, and every such bundle has the geometric properties. -/
theorem sourceDefinitionEquivalence : SourceDefinitionEquivalence.{u} := by
  apply sourceDefinitionEquivalence_of_inverse_isMonHom
  intro S G hG
  let : Smooth G.X.hom := hG.1
  let : IsProper G.X.hom := hG.2.1
  exact pointedMorphismRigidity S G G hG inferInstance inferInstance inferInstance
    ι[G.X] GrpObj.one_inv

end Langlands.AbelianScheme
