# Descent of finitely many field-valued points of a finite scheme

`Langlands.AlgebraicGeometry.FiniteFieldPointDescentStatement` starts with a
finitely generated \(\mathbf Z\)-subalgebra `C` of a field `K` and a scheme `Y`
finite over `Spec C`. Any finite family of `K`-points of `Y` over `C` comes
from points over a single finitely generated subalgebra `D` of `K` containing
`C`. The statement records the comparison by precomposition with
`Spec K ⟶ Spec D`, using the actual points in the slice over `Spec C`.

The theorem `finiteFieldPointDescent` proves the statement using the
finite coordinate algebra of `Y`. Choose finitely many `C`-module
generators of this algebra. Adjoin to `C` the images of these generators
under the coordinate maps of all the points. These images form a finite
set because both the family of points and the generators are finite.
The image of the entire coordinate algebra under each map then lies in
`D` by span induction. Corestricting the coordinate maps and applying
`Spec` gives the points and the required equalities.

The statement is a finite-morphism instance of descent of morphisms
along affine inverse limits. The source is the Stacks Project,
*Limits of Schemes*, Lemma 32.10.1(2) (tag `01ZM`), `limits.tex` at
commit `a04446e57ec1fbc252a871afcec7752fb2807b14`. The registered
folder is `stacks-limits-of-schemes-a04446e5`, content SHA-256
`2f8053f028d2ef75bb776f1863aedfba4ce578ae6999eaa60f88cd93100cf453`.
