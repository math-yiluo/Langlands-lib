import Langlands.GroupScheme.Reductive.SplitRootReflectionReduction
import Langlands.GroupScheme.Reductive.SplitWeylRationality
import Langlands.GroupScheme.Reductive.RootDatumFiniteWeylAssembly
import Langlands.GroupScheme.Reductive.RootReducednessProof

/-! # Existence of the root datum of a split maximal torus -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Root datum existence from Weyl-group rationality.** Rationality of the Weyl group of a
split maximal torus gives integral reflection data; together with the finite Weyl image and
reducedness of the roots, this gives a finite reduced root datum of the torus. -/
theorem rootDatumExistence_of_splitWeylRationality
    (hW : SplitMaximalTorusWeylRationalityStatement.{u}) :
    RootDatumExistenceStatement.{u} := by
  intro k _ G hG T hT i hi
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.2.1.mono
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : Finite (weylImage i) := splitTorusWeylImageFinite k G T hT i hi.2.1
  exact exists_rootDatum_of_reflectionData_of_finite_weylImage i hG hT
    (SplitWeylRationality.reflectionData hW hG hT i hi) (rootReducedness k G hG T hT i hi)

/-- **Existence of the root datum** (Milne, *Algebraic Groups* (2017), Theorem 21.11 and
Corollary 21.12). A split maximal torus of a connected reductive group over a field has a
finite reduced root datum. -/
theorem rootDatumExistence : RootDatumExistenceStatement.{u} :=
  rootDatumExistence_of_splitWeylRationality splitMaximalTorusWeylRationality

end Langlands.GroupScheme
