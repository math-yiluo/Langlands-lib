# Isomorphism classes of the actual Picard groupoid

This internal comparison quotients the objects of `PicardGroupoid X` by ordinary
isomorphism and identifies that quotient with the published `Group X`. The
forward map takes the class of the underlying actual line bundle. Its inverse
uses the existing chosen line-bundle representative of a Picard group element.
The inverse equations use the published criterion that two actual line bundles
have the same class exactly when they are isomorphic.

`pseudofunctorIsoClasses` constructs the functor of isomorphism classes of any
Cat-valued pseudofunctor on a locally discrete category. Its functor laws follow
from the unit and composition comparison isomorphisms. Applied to the actual
Picard groupoid, the quotient comparison is natural for every scheme morphism.
Precomposition with the base-change family gives `relativeClassPresheafIso` on
all schemes over the base. Applying fppf sheafification gives
`relativeClassSheafIso` to the exact published `RelativePicard.classSheaf`.
The comparison commutes with the two sheafification units by their naturality.
In particular, the image of an actual line bundle is exactly its published
`RelativePicard.sheafClassOf`, as stated in
`relativeToClassSheaf_comparison_isoClass`.

The construction makes no restrictions on test schemes or field hypotheses.
It supplies only the comparison for **fppf** sheafification. Artin's corrected
argument in the 1974 Appendix uses the etale sheaf of isomorphism classes; the
comparison between those two topologies, stack descent, algebraicity and the
atlas remain separate obligations.
