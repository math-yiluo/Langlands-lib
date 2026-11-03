# Uniform all-test solvability and geometric solvability

This internal supporting unit relates the two existing solvability predicates
used by the ordered-product and structural group-scheme developments. It does
not introduce a replacement predicate.

For a group scheme `G` over an arbitrary scheme `B` in universe `u`,
`IsSolvableScheme.uniformBound` chooses a natural number from the existing
assertion that one derived-series bound works on every test scheme over `B`.
The choice need not be minimal. `derivedSeries_uniformBound` records its
defining property, and `points` supplies abstract solvability of each actual
point group.

The elementary group lemmas retain the supplied numerical bounds. An injective
homomorphism inherits the target's bound because the image of each derived
series term lies in the corresponding target term. If the kernel of
`q : P →* K` lies in the image of `f : N →* P`, bounds `m` for `N` and `n`
for `K` give bound `n + m` for `P`. The `n`th term of `P` lies in that image;
induction through commutators bounds each subsequent term by the image of
the corresponding term of `N`. Neither pointwise surjectivity of `q` nor
injectivity of `f` is needed.

Consequently a monomorphism of group schemes inherits a uniform bound,
and actual group-scheme isomorphisms preserve uniform solvability in both
directions. Base change along any morphism of base schemes preserves the
same chosen bound: use `baseChangePointsEquiv` on each test over the new base.
These results require no field, smoothness, affineness or connectedness.

For any actual automorphic action of a uniformly solvable group scheme `K`
on a uniformly solvable group scheme `N`, the semidirect product is uniformly
solvable. Use the standard normal inclusion and acting-coordinate projection
on each semidirect point group. Their exact kernel/image identity and the
extension bound give the sum of the two fixed bounds. Transfer this bound
through `semidirectPointsEquiv`. This argument applies to every test scheme,
including nonreduced tests.

Over any field `k`, uniform all-test solvability implies the existing
`IsSolvableGroupScheme` predicate. Evaluate at the algebraic-closure point over
the original base, and use the actual base-change point equivalence to recover
the point group used in that predicate. This implication has no geometric
regularity premise. Conversely, for a smooth affine group, the published
`SolvableFieldExtensionProof.exists_uniform_derivedSeries_eq_bot` gives the
required uniform bound. The resulting equivalence needs neither connectedness
nor an algebraically closed base. The converse reuses that theorem's
derived-word and geometric-point equality argument; this unit does not repeat it.

The provenance is internal: choice from the existing uniform-solvability
existential, functoriality of abstract derived series, the standard semidirect
kernel identity, actual point equivalences and the published uniform-bound
theorem. This closes the solvability-interface gap needed to apply structural
results to the root-product target. It proves no compatible solvable
decomposition, scalar descent of ordered products, or full
`SemigroupOrderedProductStatement`.
