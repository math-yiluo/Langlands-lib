import Langlands.GroupScheme.Absolute.BorelAlgClosedFieldExtensionStatement
import Langlands.GroupScheme.Absolute.BorelFieldExtensionFields
import Langlands.GroupScheme.Absolute.BorelFieldExtensionMaximality

/-! # Borel subgroups under extensions of algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An extension of algebraically closed fields preserves Borel subgroup inclusions in smooth
connected affine group schemes. -/
theorem borelAlgClosedFieldExtensionStatement : BorelAlgClosedFieldExtensionStatement.{u} := by
  intro k K _ _ _ _ _ G hG hsm _ B i hi
  have : IsAffineHom G.X.hom := hG
  have : Smooth G.X.hom := hsm
  exact BorelFieldExtension.isBorelSubgroup_baseChange_of_maximal _ hi
    (fun B' i' f h1 h2 h3 h4 h5 => BorelFieldExtension.maximal_baseChange hi B' i' f h1 h2 h3 h4 h5)

end Langlands.GroupScheme
