# Flath factorization for the actual restricted product

`Langlands.flathRestrictedProductExistence` proves the exact published
`Langlands.FlathRestrictedProductExistenceStatement`, with independent index,
local-group and ambient-carrier universes. It constructs admissible irreducible
local factors in the original carrier universe and an actual equivariant linear
equivalence to their restricted tensor product. Outside one finite exceptional
set, the chosen reference vectors are nonzero and fixed by the reference
subgroups, whose full fixed spaces have dimension one.

The proof first applies `flathCyclicVectorSelection`. This supplies a common
nonzero ambient vector, fixed by the entire complementary reference tail, whose
coordinate orbit spans are admissible and irreducible. These subspaces are
bundled as `ModuleCat` objects in the ambient carrier universe. Their generators
give the reference vectors, and the selected fixed-space dimensions supply the
almost-everywhere fixed-line conclusion.

Admissible Schur makes every local self-intertwiner scalar. Together with
ambient and local irreducibility, nonzero generator and full-tail fixedness,
these facts discharge every hypothesis of `CyclicEvaluation.evalEquiv`. This
is an equivalence from the actual cyclic restricted tensor representation to
the ambient representation; its equivariance includes infinitely supported
reference tails.

The evaluation construction uses the generator at every coordinate, whereas
`ReferenceVectors.family` fills exceptional coordinates with zero. These
families agree outside the finite exceptional set. The published `change`
linear equivalence changes those finitely many reference coordinates.
`map_intertwines`, applied to identity local maps, makes this a representation
equivalence. Composing it with inverse evaluation gives the exact orientation
and the exact `productRepresentation` required by the conclusion.

The provenance is the internal composition of the selection, evaluation,
admissible Schur and restricted tensor change-of-reference results. The source
of the target is D. Flath, *Decomposition of representations into tensor
products*, Proc. Sympos. Pure Math. 33, part 1 (1979), Theorem 2, printed p.181;
the construction is in section 2, pp.180–181. The target's companion Markdown
records the registered original and the topological and spherical-convolution
conventions. This proof preserves those hypotheses and adds no countability,
unimodularity, normalization, finite-index or nonempty-index assumption.
It proves the existence assertion; uniqueness remains a separate statement.
