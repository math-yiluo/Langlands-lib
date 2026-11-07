# Original semidirect projections as dynamic limits

This internal helper concerns an affine group scheme over a field, three actual rational-point subgroups `P`, `M`, `U`, and any original semidirect decomposition of those subgroups. A specified cocharacter must identify the three subgroups with its dynamic parabolic, centralizer and unipotent rational points. These identifications remain explicit.

`projection_eq_dynamicLimit` identifies the original Levi projection with the dynamic limit. The limit lies in `M`, and the dynamic radical identity implies that its inverse times the original point lies in `U`. Uniqueness of the original semidirect factorization proves equality. This generalizes the existing standard-subgroup proof in `RationalParabolicDecomposition` to arbitrary actual subgroups; no standard parabolic presentation is used.

`projection_mem_of_closed_stable` applies that equality to any subgroup functor represented by a closed subgroup inclusion and stable under conjugation by the realizing cocharacter. The existing closed-stable limit membership theorem puts the dynamic limit, hence the original projection, in that same subgroup. Closedness here is the algebraic closed-subgroup condition, rather than a supplied topological closedness assertion.

`closedStableProjection` is the resulting homomorphism from the original
parabolic intersection with that subgroup to its original Levi intersection.
The domain and codomain are the literal `subgroupOf` restrictions of its
rational points, and its underlying map is exactly the original projection.
The displayed application formula records this identity on every point.

`projection_mem_commonTorusUnipotent` specializes this argument to the dynamic unipotent subgroup of another cocharacter of the same commutative group scheme. The existing conjugation-stability theorem and affine dynamic representation supply the required stability and closed representation.

The proof uses no topology on the field, local compactness, root-system hypothesis or character detection. It does not prove existence of the realizing cocharacter, identify a stabilizer image, or establish a geometric-lemma orbit comparison.
