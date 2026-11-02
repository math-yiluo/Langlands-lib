# Quotient and coefficient-map statements for affine point topologies

Author: Worker 105.

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1, printed page 2, and Example 2.2,
printed page 3. Registered source `conrad-2011-weil-grothendieck-adelic-points`,
SHA256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

These are proposition-valued statement targets over the constructed actual
algebra-map point spaces, in namespace
`Langlands.AlgebraicGeometry.PointTopology`.

`QuotientPointEmbeddingProperties R A B S` states that precomposition by a
surjective map of commutative `R`-algebras `A → B` embeds `B`-points into
`A`-points. If the value ring `S` is Hausdorff, this embedding is closed.
Neither coordinate algebra needs to be finitely generated, and no continuity
of ring operations is needed for this intrinsic quotient assertion. It is
the algebra-map form of the affine closed-immersion assertion in
Proposition 2.1; its scheme closed-immersion comparison remains separate.

`CoefficientEmbeddingProperties R A S T` states that an embedding, or a
closed embedding, of value rings `S → T` induces the corresponding map on
actual affine points by composition. No finite-type or Hausdorff assumption
is needed for these intrinsic assertions.

`CoefficientOpenEmbeddingProperty R A S T` uses topological rings `S` and `T`.
It asserts that an open embedding of coefficients induces an open embedding
on affine points if `A` is of finite type over `R`.
`AffineDiscreteProperty R A S` states that finite-type affine points over a
discrete topological value ring are discrete. Together with the embedding
assertion this supplies the discrete-subspace implication of Example 2.2.

The map direction is always `S → T`, and its point map is `X(S) → X(T)`.
Thus it is `S` which is viewed as the closed, open or discrete subring of
`T`, correcting the reversed ring inclusion in Example 2.2. The relative
base ring `R` has no topology and its coefficients are fixed constants.
Taking `S = R` gives the source's coefficient-change situation. These
statements are not proofs or a whole-paper completion claim.

`AffineMapProperties R A B S T` groups these four targets, quantifying
topological-ring and discreteness instances only in the corresponding
open-embedding and discreteness clauses.
