# Closedness of a centralizer times a Borel containing its cocharacter

Authors: Worker 1438 and Worker 1333.

This internal composition constructs
`IsBorelSubgroup.centralizerProductClosurePointLift` and proves
`IsBorelSubgroup.centralizer_product_isClosed` in the scope of the published
`CentralizerBorelIntersectionStatement`. Let `k : Type u` be an algebraically
closed field and `G` a smooth connected affine group scheme over `k`. Let
`χ : Gm → G` be any cocharacter and let the supplied closed inclusion
`j : M → G` represent the full subgroup functor `Dynamic.centralizer χ`.
Assume the specified smoothness and connectedness of `M`. If `b : B → G` is
a Borel subgroup containing the range of `χ` on every relative scheme test,
then the actual underlying image of the multiplication morphism
`CentralizerProduct.productHom j b : M × B → G` is closed.

The theorem retains no quotient-existence, kernel-splitting or conjugacy
premise. The universe and characteristic are arbitrary. Trivial and
noninjective cocharacters and every supplied closed centralizer
representative are included. Closedness concerns the topological image of
the actual scheme morphism.

For each rational point `a : Spec k → CentralizerProduct.imageClosure j b`
of the reduced image closure, `centralizerProductClosurePointLift` chooses
an actual rational point of `M × B`. The theorem
`centralizerProductClosurePointLift_comp` proves that its image under the
multiplication morphism is `a` followed by the closure inclusion into `G`.
The definition uses classical choice from the proved factorization; it
asserts no uniqueness or compatibility as `a` varies, and it does not
construct a section of schemes. The lift and its factorization theorem
only need affineness of the ambient `G`, alongside the other stated
Borel, centralizer, smoothness and connectedness data. Ambient smoothness
is used for the image-closedness conclusion. Ambient connectedness is
unnecessary for both results; in particular, they cover the original
smooth connected ambient scope.

The proof first gets smoothness, connectedness and solvability of `B` from
its Borel structure. The affine structure of `G` makes its underlying
scheme quasi-compact. Closedness inside `G` makes both `B` and `M` affine,
and gives monicity of the underlying inclusion of `B`.
The published reduction
`solvableTorusQuotient_of_kernel_prerequisites`, instantiated with the
published proofs `triangularDiagonalKernelGeometry` and
`unipotentClosedSubgroup`, supplies actual group schemes `U,D`, a closed
inclusion `n : U → B` and a represented fppf quotient `q : B → D`.
Here `D` is a split torus, and `U` is smooth, connected and unipotent.
The quotient predicate retains equality of the full kernel range with the
range of `n` on all relative scheme tests. Closedness makes `U` affine, so
the published `Unipotent.algebraicallyClosedSplit` gives its represented
split-unipotent series.

For any `ψ : Gm → B` with the same projection under `q` as the restricted
cocharacter `Dynamic.restrictCocharacter b χ hχ`, the theorem
`homConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements`
gives `HomConjugate` of these actual homomorphisms. Its three structural
premises are all supplied by published proofs:
`RelativeRoot.splitUnipotentStableVectorSubgroup`,
`RelativeRoot.torusVectorActionLinearization` and
`splitUnipotentAffineTorsorStatement`. The source torus condition follows
from `isSplitTorus_gm.isTorus`. This comparison fixes the source and
requires neither cocharacter to be monic.

The published
`CentralizerProduct.closure_point_factors_of_same_projection` applies to
`q`, its split torus target, and this conjugacy callback. It supplies the
factorization used by the chosen lift and its factorization theorem.
Finally, `CentralizerProduct.product_image_isClosed_of_closure_points`
applies to these lifts. Its constructible-image and Jacobson closed-point
argument proves the asserted closedness of the actual multiplication
image.

The provenance is entirely this composition of existing Library results.
Worker 1333 supplied the same-source conjugacy route. This module adds no
new structural assertion from the literature. It discharges the closed
product input to `centralizerBorelIntersection_of_closed_products`; the
properness and proper-solvable-quotient Borel criterion used by that
reduction remain separate obligations. This module does not prove the full
Borel-intersection target.
