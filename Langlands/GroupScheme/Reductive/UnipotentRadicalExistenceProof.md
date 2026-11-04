# Existence of the represented ground-field unipotent radical

`Langlands.GroupScheme.unipotentRadicalExistence.{u}` proves the published
`UnipotentRadicalExistenceStatement.{u}`. For every field `k : Type u` and
every smooth connected affine group scheme `G` over `Spec k`, it supplies an
actual group scheme `U` and homomorphism `i : U ⟶ G` satisfying the unchanged
`IsUnipotentRadical i`. There is no additional theorem-valued premise.

The proof uses the published finite-height maximality helpers. Smoothness of
`G` supplies local finite type, and its affine structure morphism makes its
underlying scheme affine. The trivial subgroup makes the class of smooth
connected normal unipotent closed subgroups nonempty. The helper
`exists_minimal_height_candidate` chooses a candidate whose prime coordinate
kernel has the least finite height.

For this candidate `i : U ⟶ G` and any competing candidate `j : V ⟶ G`,
the published `smoothConnectedNormalFppfProductExistence` constructs an actual
smooth connected group scheme `P` with a closed homomorphism `p : P ⟶ G`
representing their ordered fppf-local product. Both factors are affine because
their closed inclusions have affine target. The published
`isUnipotent_fppfProduct` therefore proves `IsUnipotent P` from their
unipotence and normality of the first range. The product normality law proves
normality of the range of `p`. Thus `p` is another candidate, and the two
product containment laws give a common candidate upper bound.

The helper `isUnipotentRadical_of_minimal_height` now proves greatestness.
Minimal coordinate-kernel height makes the inclusion of `U` in this upper
bound an isomorphism, hence identifies their ranges. Containment of the
competitor in the product then gives containment in the range of `i`.
All these ranges, normality conditions and containments use every relative
scheme test, including nonaffine and nonreduced tests. The remaining five
fields of the radical predicate are exactly the chosen candidate's fields.

This is the ground-field radical. The proof assumes no perfectness or
characteristic restriction on the field and asserts neither splitness nor
compatibility with the geometric radical after extending the field.
It changes neither the target nor its imported definitions.

The provenance of this assembly is internal composition of the imported
Library results. Their paired Markdown documents the finite-height
maximality, common-fixed-vector and product-unipotence arguments, and the
semidirect-image construction of the represented product. Worker 1353
authored the assembly, maximality and fixed-vector descent helpers.
Worker 1328 contributed the common-fixed-vector and product-unipotence
development used in the assembly.
