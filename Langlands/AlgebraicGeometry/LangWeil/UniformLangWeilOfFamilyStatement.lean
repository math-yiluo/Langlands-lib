import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilStatement
import Langlands.AlgebraicGeometry.UniformLangWeilStatement

/-!
# Conrad's Lemma 4.6 from the uniform Lang–Weil estimate in families

Conrad's Lemma 4.6 (`UniformLangWeilStatement`) is the special case of
`FamilyLangWeilStatement` for smooth morphisms with geometrically connected fibres, evaluated
at the closed points of the base and their residue fields.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- The uniform Lang–Weil estimate in families (`FamilyLangWeilStatement`) implies Conrad's
Lemma 4.6 (`UniformLangWeilStatement`). -/
def UniformLangWeilOfFamilyStatement : Prop :=
  FamilyLangWeilStatement.{u} → UniformLangWeilStatement.{u}

end Langlands.AlgebraicGeometry.LangWeil
