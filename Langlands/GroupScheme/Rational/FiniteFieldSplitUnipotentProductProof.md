# Finite-field split-unipotent product criterion

`Langlands.GroupScheme.RelativeRoot.finiteFieldSplitUnipotentProduct.{u}` proves
the unchanged published proposition
`Langlands.GroupScheme.RelativeRoot.FiniteFieldSplitUnipotentProductStatement.{u}`.
It works over every finite field `k : Type u`, in arbitrary characteristic,
with the actual smooth connected affine split unipotent groups and closed
subgroup maps in that proposition. Its conclusion concerns the original
`subgroupMultiplication j c` as a morphism of schemes.

Write `E = subgroupIntersection j c` for the actual scheme-theoretic
intersection. Its smoothness and connectedness are hypotheses of the target;
its affineness follows from the closed projection to the affine first factor.
The published rational-point counting theorem applies the given surjectivity on
`k`-rational points and the finite additive-group series for `V`, `C`, `U`, and
`E`. It gives
`dim V + dim C = dim U + dim E`, with dimensions computed by the original
dual-number Lie kernels.

The proof then passes to `K = AlgebraicClosure k`. Smoothness and affineness of
the three groups persist under pullback. Their smooth affine connected
structures give connectedness after this field extension. The canonical
intersection base-change isomorphism identifies the pullback of `E` with the
actual intersection of the pulled-back maps; it transports smoothness to that
intersection. The published Lie dimension base-change formula and invariance
under this actual group-scheme isomorphism transport the dimension equality.
The split series of the two factors also pull back, and give their
representation-theoretic unipotence over `K`.

`ProductGeometry.smooth_surjective_subgroupMultiplication_of_lie_dimension`
now applies to the pulled-back groups and subgroup maps. Its proof uses the
actual action `(v,z) · x = j(v) x c(z)⁻¹`, with diagonal intersection stabilizer
and exact coset fibers on every scheme test. Unipotence makes this orbit closed;
the dimension equality makes its inclusion into the reduced connected smooth
target an isomorphism. Its smooth stabilizer gives a smooth surjective orbit
map. Inverting the second factor identifies this map with the original
multiplication after base change.

Finally, the canonical product-comparison isomorphism identifies multiplication
of the pulled-back subgroups with the pullback of the original multiplication.
The field extension is faithfully flat and quasi-compact. Smoothness descends
through this cartesian square, and surjectivity reflects along the surjective
base change. This proves exactly smoothness and underlying-scheme surjectivity
of the original morphism over `k`.

The implementation derives every geometric input from the target hypotheses.
It adds no dimension, closure, dominance, or geometric connectedness premise.
The all-test identities used for intersections and orbit fibers retain
nonreduced test schemes; the conclusion asserts scheme surjectivity and does
not require lifting every point on every test without a cover. This is an
internal proof assembled from the imported counting, product-action,
dimension, intersection, and descent results.
