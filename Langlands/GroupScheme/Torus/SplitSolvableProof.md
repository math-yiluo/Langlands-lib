# Every split torus is split solvable

Authors: Worker 1435, Worker 1295, and Worker 1472.

The final theorem `Langlands.GroupScheme.splitTorusSplitSolvable` proves the
unchanged published proposition `SplitTorusSplitSolvableStatement.{u}`. For
every field `k : Type u` and actual group scheme `T` over `Spec k`, its only
hypothesis is `IsSplitTorus T`. The conclusion is the full published
`IsSplitSolvableGroupScheme T`, including its finite represented Ga/Gm-series.
There are no restrictions on characteristic, perfection, cardinality of the
field, or the rank of the split torus.

The proof is an internal derivation from the published split-torus point
models, product geometry and split-solvable definitions. It introduces no
external assertion. Worker 1295 supplied the checked all-test empty case and
a parallel series-transport draft. Worker 1472 contributed the finite-index
induction and geometric-point solvability and final assembly. Worker 1435
constructed and checked the product geometry and combined the proof.

`SplitSolvable.HasSeries.of_iso` transports a represented series along an
actual group-scheme isomorphism. In length zero, the inverse isomorphism is
injective on points of every relative test, so it preserves all-test
triviality. In positive length, it postcomposes the inclusion and precomposes
the quotient with the appropriate isomorphisms; the subgroup and quotient
objects themselves are unchanged. Closed immersions compose with
isomorphisms, and the published range and fppf quotient transport lemmas
preserve normality and the exact kernel. The argument adapts the published
Ga-only transport in `Rational.SplitUnipotentTransport` to the existing
Ga/Gm-series predicate.

For group schemes `A` and `B` over a field, the geometric helpers use the
actual inclusion `lift (𝟙 A) (0 : A ⟶ B)` and projection `snd A B`. The first
inclusion is a section of the separated first projection, so it is a closed
immersion. Separatedness follows from the published field-separatedness
result and base change. The kernel of the second projection is precisely
the range of this inclusion on every relative scheme: a point whose second
coordinate is the identity is recovered by including its first coordinate.
The second projection preserves multiplication and inverses; applying it to
a conjugate proves all-test normality of its kernel.

When `A` is smooth, the second projection is smooth by base change, hence
flat and locally of finite presentation. It is surjective because it has
the actual section `lift (0 : B ⟶ A) (𝟙 B)`. Together with the kernel equality,
this gives exactly the unchanged `RelativeRoot.IsFppfQuotient` predicate.
Specializing to `B = Gm` adjoins one elementary quotient to a series on a
split torus `A`; its required smoothness and connectedness come from the
published split-torus results. Every quotient in the constructed series is
Gm, which is one of the permitted elementary factors.

`hasSeries_splitTorus_empty` establishes the rank-zero base case by using
the natural unit-coordinate equivalence on every relative test: an empty
family of units has only one value. `exists_hasSeries_splitTorus` then uses
finite-type induction with empty and `Option` cases. The published
`piEquivIso` handles reindexing. The `Option` product isomorphism, together
with the symmetry of the product, reduces the successor to the preceding
product tensored with one Gm. Series transport then supplies the required
series on the original finite product.

For solvability, base change the split presentation to the algebraic closure
and evaluate its natural unit-coordinate equivalence on the base-point test
scheme. The composite equivalence supplies an injective homomorphism from geometric
points into a family of unit groups of a commutative ring. That family is
commutative, so Mathlib supplies its solvability, which transfers along the
injective homomorphism. This proves precisely `IsSolvableGroupScheme T`.

Finally, the published `IsSplitTorus.smooth`,
`IsSplitTorus.isAffineHom`, and `IsSplitTorus.connectedSpace` supply the outer
geometry. The isomorphism in `IsSplitTorus T` transports the finite-product
series back to `T`. These facts and geometric-point solvability assemble
`IsSplitSolvableGroupScheme T`; the final theorem packages this implication
at arbitrary universe `u`. The published definitions and target statement
are unchanged.
