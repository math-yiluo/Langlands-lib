# Irreducibility of the entire canonical space at a Steinberg height

This derived unit combines the actual highest-vector Frobenius orbit with
the full canonical covariant-space upper bound and the eigen-row coefficient
construction. It supplies the per-height input to the cofinal assembly.

Work over an algebraically closed field `k : Type u`, with an actual affine
group scheme `G`, a supplied split pinning `p` with finite root index, and
full integral coroot span `hspan`. Let `rho` be the integral Weyl vector,
`nu` its polarization and `chi` the canonical negative-rho coordinate on
the represented dynamic parabolic of `groupHom nu` followed by the original
torus inclusion. Let `q` be an exponential characteristic and `r` any natural
height. Supply an actual highest-weight matrix representation on a finite
index `n`, at weight `(q^r - 1) • rho`.

`highestWeight_finrank_ge_rootCount` proves that the dimension of its whole
coordinate space is at least `(q^r)^N`, where `N` is the number of positive
roots of the supplied base. Its one-dimensional highest-weight space contains
a nonzero vector. The actual opposite-unipotent Frobenius orbit at that vector
has dimension `(q^r)^N` by `HighestWeightFrobeniusOrbit`, and it is a subspace
of the original coordinate space. This gives the lower bound.

Reductive smoothness follows from the supplied pinning. The proved
`SmoothReducedProof.isReduced_of_smooth_over_field` gives reducedness of `G`,
and smoothness gives local finite type. Over the algebraically closed field,
`IsIrreducible.rationalRepresentation` therefore converts the actual
irreducibility included in the highest-weight predicate to irreducibility of
the same rational-point action.

`scalarRhoEigenrowData` gives a rationally irreducible conjugated dual on the
same index `n`, with nonzero row and all-relative-test eigen-row character
`chi^(q^r-1)`. In particular its coordinate dimension is exactly that used by
the lower bound. The upper bound from `CanonicalRhoRootDimension` applies to
the entire canonical covariant space at the same height. Its finite
dimensionality is already proved by same-height Frobenius restriction.
The existing coefficient-exhaustion theorem thus identifies the eigen-row
coefficient map with that whole space.

`canonicalRhoSteinbergCoefficientEquiv` constructs the resulting linear
equivalence from `n → k` to the entire canonical covariant space. The chosen
conjugated dual supplies the source action for the coefficient construction;
the equivalence does not assert that the original highest-weight action has
the same weight or action as its dual.

`canonicalRhoSteinberg_regular_rationalRepresentation_isIrreducible` applies
the same exhaustion theorem in every supplied finite basis of the entire
covariant space. The original coefficient map intertwines the rational action
of the conjugated dual with the actual Chevalley right regular action in that
basis, so the latter is irreducible, including its nontriviality requirement.
No separate dimension or irreducibility hypothesis on the target is supplied.

`canonicalRhoSteinbergHeightIrreducibility` directly instantiates the
`CanonicalRhoSteinbergHeightIrreducibility` proposition used in
`CanonicalRhoSteinbergAssembly`. The proof works at every height, and hence
also at the positive heights quantified in that interface.

The field universe is arbitrary. The eigen-row, coefficient covariance and
geometric constructions retain arbitrary relative scheme tests, including
nonaffine and nonreduced tests. The final representation predicate is the
original rational-point irreducibility used by the host statement.
The split pinning, full coroot span and highest-weight module remain supplied.
Their universal existence and `SteinbergBigCellStatement` are not proved in
this unit. Its provenance consists entirely of the named imported proofs and
the finite-dimensional comparison described above.

The accompanying integration change names the two local affine instances in
`HighestWeightFrobeniusOrbit` explicitly. This prevents generated declaration
names from colliding with `CanonicalRhoUnipotentRestriction` when both proof
routes are imported here; it changes no mathematical declaration or proof.
