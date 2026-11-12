# Actual ordered object filtrations from Haar-correction cancellation

Author: Worker 124.

This module constructs actual `PointGeometricObjectFiltration` data from one
remaining explicit hypothesis: cancellation of the original two epsilon Haar
corrections at every minimal representative and every lift. It does not prove
that cancellation. The construction applies to all standard source and target
subsets and all smooth inducing objects, with no maximality, cuspidality,
irreducibility, admissibility, reducibility or finite-length premise.

## Actual orbit order and identity endpoint

`pointMinimalOrbitOrderingIdentityLast` constructs a positive finite orbit
count `N + 1`, a bijection `e` with `minimalReps actual I J`, and an actual
`Geometric.OrderedDoubleCosets P_J P_I (N + 1)` cover with representatives
exactly the chosen lifts of `(e q).val`. If `I = J`, its final class is `1`.
The group is the actual `RationalPoint k G.X` with canonical `pointTopology`,
not an abstract replacement. Local compactness, nonarchimedean structure and
Hausdorffness are explicit; the field is any nonarchimedean local field.

The proof derives second countability with
`reductiveRationalPoint_secondCountable` and closed parabolics with
`isClosed_standard_parabolic`. It invokes the existing `minimalOrbitOrdering`
with the unconditional `GroupScheme.standardParabolicPointsStatement_proof`.
That theorem proves finiteness and the bijective classification of actual
`P_J \ G / P_I` orbits by the inverse minimal representatives of
`W_I \ W / W_J`. The count is positive because the minimal set contains `1`.
No point-Bruhat proposition is added as an extra assumption here.

For a self composite, the unique index of class `1` has its representative in
the actual Levi, by `normalizerLift_mem_levi_of_mk_eq_one`, and hence in its
parabolic. `cosetOrbit_self_eq_singleton` identifies the orbit as the singleton
identity coset. `QuotientIntegration.leftQuotient_t2Space` makes the quotient
Hausdorff from the derived closedness of the parabolic, so the singleton is
closed. The proved `OrderedDoubleCosets.closedOrbitLast` constructs an orbit
ordering with it last, preserving open initial unions and the relative order
of the other orbits. Composing the enumeration with that permutation preserves
its exact chosen lifts. The refinement occurs before applying the support
filtration, so it does not permute the factors of an existing extension.

## Actual filtration and grade isomorphisms

`pointGeometricObjectFiltrationOfEpsilonBalance` constructs the full datum for
an arbitrary smooth `σ`. The two independent universes remain `u` and `v`, and
carriers have universe `max (u + 1) v`.

Its additional `hε` hypothesis is precisely the identity of characters

```text
geometricEpsilonOne i ν I J dI dJ n (hU J) (hP I) *
  geometricEpsilonTwo i ν I J dI dJ n (hU I) (hP J) = 1
```

for every `w ∈ minimalReps actual I J` and every actual lift `n` of `w`.
Here `dI`, `dJ` are the original standard semidirect decompositions and `hP`
is the derived actual closed-parabolic proof. Trivial input characters are
not used to erase these corrections.

From the displayed root-length and positive-simple comparisons,
`pointSourceIntersectionIdentities` and
`geometricIntersectionDecompositions_of_pointSource` derive the actual source
and target semidirect decompositions at every minimum lift. Projection
continuity is derived by `continuous_standard_projection`. Compact-subgroup
limits for the actual radicals come from
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.
These are conclusions of published theorems applied to the existing standard
cocharacter premise, not extra construction hypotheses.

Choose one normalizer lift of each actual Weyl class and use the preceding
orbit-order construction. `jacquetSupportFiltration` is then evaluated at `σ`
with `RepFunctorFiltration.atObject` to obtain the actual finite filtration of
`r_I(i_J σ)`. At every index, `jacquetSupportGeometricTermIso`, applied to the
same lift, decompositions, topology proofs and `hε`, gives the actual normalized
geometric-term grade comparison; evaluation at `σ` supplies the datum's grade
isomorphism. The orbit enumeration and final-identity property are retained
unchanged. All representatives, decompositions, filtration steps and grade
isomorphisms are therefore constructed, conditional only on the stated epsilon
cancellation and the displayed structural/Coxeter/topological data.

## Provenance and dependency boundary

This is an internal composition of the existing actual orbit classification,
actual support filtration and normalized orbit comparison, with the generic
closed-orbit ordering refinement. `StandardParabolicPointsStatement` is
proved by `standardParabolicPointsStatement_proof` from `rationalBruhat` and
`rootRankOneFactorization`, via the relative Tits realization and standard
parabolic order/endpoints; it is not an assumed geometric lemma.
`jacquetSupportGeometricTermIso` is the normalized orbit-grade comparison
published in [RationalGeometricOrbitTerm](RationalGeometricOrbitTerm.md).
Its proof uses the actual compact Mackey support filtration and exact
coinvariants (`jacquetSupportOrbitIso`), the actual source quotient comparison
(`orbitPieceCoinvariantsIso`), normalized compact models and the
compact/full-induction isomorphism after proving target quotient compactness.
It keeps the epsilon product until `hε` is supplied. The endpoint-order helper
is documented in [ClosedOrbitLast](../../Geometric/ClosedOrbitLast.md).

No full geometric-lemma expansion, adjointness, cuspidal-support theorem,
character independence or Langlands classification is invoked as a proved
instance by this construction. The representation-theoretic proof route is
the named Mackey/support/normalized-grade construction above. Imported modules
also contain distinct conditional finite-length and exact-K0 assemblies;
their hypotheses are not used here. The epsilon cancellation remains an
explicit hypothesis and needs its own exact published proof before this
construction proves the unconditioned maximal-source filtration proposition.
