import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilStatement
import Langlands.AlgebraicGeometry.LangWeil.FamilyPointUpperBoundStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceUniformLangWeilStatement

/-!
# The algebraic-space form of Conrad's Lemma 4.6 from the scheme estimates in families

The algebraic-space form of Conrad's Lemma 4.6 (`SpaceUniformLangWeilStatement`) follows from
the uniform Lang–Weil estimate for families of schemes and the uniform upper bound for point
counts in families, by stratifying the algebraic spaces by schemes.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- The uniform Lang–Weil estimate in families of schemes (`FamilyLangWeilStatement`) and the
uniform point-count upper bound in families (`FamilyPointUpperBoundStatement`) imply the
algebraic-space form of Conrad's Lemma 4.6 (`SpaceUniformLangWeilStatement`). -/
def SpaceUniformLangWeilOfFamilyStatement : Prop :=
  FamilyLangWeilStatement.{u} → FamilyPointUpperBoundStatement.{u} →
    AlgebraicSpace.SpaceUniformLangWeilStatement.{u}

end Langlands.AlgebraicGeometry.LangWeil
