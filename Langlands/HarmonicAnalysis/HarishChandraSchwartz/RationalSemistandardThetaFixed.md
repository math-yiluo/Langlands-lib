# Actual full semistandard fixed indices and local Levi finiteness

This module constructs the full fixed-index set for Waldspurger VIII.1.3 from
the imported intrinsic index and the actual normalized induced representation.
It states the all-Levi and proper-Levi local VIII.1.2 hypotheses separately.

## Source and actual objects

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)* (2003), printed p.321, VIII.1, Théorème VIII.1.2,
Remarque VIII.1.3(i), and its following explanation. Registered source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The local predicates and the literal-subgroup realization are derived interfaces
for applying the source at each Levi; they are not new analytic proofs.

The context is any nonarchimedean local field `F : Type u`, including positive
characteristic, with finite residue field under the Library class, and an affine
locally finite type group scheme `G`. The full carriers already import each
index's connected reductive Levi model. Their intended source application is a
connected reductive ambient group and maximal split torus; the constructions
need only the displayed imported index and model data. There is no split,
quasi-split, or positive-rank restriction. Representation universe `uV` is
independent of `u`. Topologies are the canonical rational-point topologies and
subspace topologies on the literal subgroups.

`RationalSemistandardTheta`, `RationalSemistandard.levi`, `decomposition`,
`chosenLeviModel`, its actual norm characters and split-center image, and
`OrbitClass` are imported. The group/proper distinction is imported from
`RationalSemistandardThetaParts`: `P = G` means equality of all-test subgroup
functors, and proper means `p.parabolic ≠ ⊤`. No replacement spectral index,
induced representation, orbit relation, or abstract comparison is introduced.

## Declarations and dependency ledger

The namespace is `Langlands.HarishChandraSchwartz`, with `RationalSemistandard`
qualified explicitly in the table.

| Declaration | Exact content and dependencies | Status |
| --- | --- | --- |
| `RationalSemistandard.LeviModel.LocalOrbitFiniteness m` | The published local VIII.1.2 predicate on `m.scheme`, for every split component, quotient Haar measure and compact open level. Model affineness and local finite type follow from its reductivity. | Prop-valued analytic premise. |
| `RationalSemistandard.AllLeviOrbitFiniteness` | The local predicate for every intrinsic `p` and every actual closed reductive representing model of its literal Levi. | Prop-valued all-Levi premise. |
| `RationalSemistandard.ProperLeviOrbitFiniteness` | The same predicate only when `p.IsProper`. There is no clause requiring local VIII.1.2 at a group index. | Prop-valued proper-only premise. |
| `RationalSemistandard.properLeviOrbitFiniteness_of_all` | Restricts the all-Levi premise to proper indices. | Elementary conditional adapter. |
| `RationalSemistandard.allLeviOrbitFiniteness_of_global` | Applies the published global VIII.1.2 assertion to each connected reductive Levi model. | Conditional specialization; not used by the proper finiteness adapter. |
| `RationalSemistandard.leviLevel p H`, `mem_leviLevel` | The actual level `H.comap (levi p).subtype`; its elements are exactly the literal Levi elements whose ambient value is in `H`. | Construction and definitional membership law. |
| `RationalSemistandard.isClosed_levi`, `isOpen_leviLevel`, `isCompact_leviLevel` | Closedness of the literal Levi and openness/compactness of its actual intersection level. | Closed geometric/topological adapters from the published closed-representative point theorem. |
| `RationalSemistandard.finite_fixedOrbits_of_local` | Transfers local VIII.1.2 for one model to the orbit set on the literal Levi, with the prescribed split center, Borel quotient and Haar measure. | Conditional model-transfer theorem. |
| `RationalSemistandard.inducedFixedVector_unitaryOrbit_iff` | An actual member of the unitary unramified orbit has nonzero induced `H`-fixed vectors exactly when the base representative does, provided `H ≤ d.compact`. | Closed specialization of the published twist transport, using the displayed compact data. |
| `rationalSemistandardThetaFixed a ha mu H` | Full `Theta^H`, as the dependent set of actual semistandard indices and unitary discrete-series orbits for which some member's actual normalized induction has nonzero `H`-fixed vectors. | Construction. |
| `mem_rationalSemistandardThetaFixed` | Membership is exactly membership in the existing `inducedDiscreteSeriesFixedOrbits` at that intrinsic index. | Elementary law. |
| `rationalSemistandardThetaFixed_antitone` | Shrinking `H` enlarges the fixed-index set. | Closed elementary adapter. |
| `mem_rationalSemistandardThetaFixed_iff_of_le` | At `H ≤ (d p).compact`, membership is equivalent to nonzero fixed vectors for any actual discrete-series object representing the same orbit. | Closed representative-independence adapter from the published compact-picture transport. |
| `RationalSemistandardFixedOrbitIndependenceStatement a ha mu` | The same any-representative equivalence at every compact open `H`, without assuming containment in a supplied compact picture. | Explicit unproved comparison target. |

The supplied family data `a,ha,mu` retain all chosen split components, normality
of their actual center images, quotient measurable spaces and Haar measures.
They contain no spectral-finiteness field. The literal-Levi finiteness theorem
additionally requires the Borel quotient structure and compact/open proofs of
its level, so arbitrary measurable quotients are not silently identified with
Borel quotients. The local predicates quantify all split components and levels;
they do not refer just to the family's selected component or measure.

## Implemented proofs and remaining comparison

The literal Levi is closed by its actual closed representing inclusion. Pulling
back an open level along its subtype inclusion proves openness, and the closed
embedding's compact-preimage theorem proves compactness of the intersection.

For model transfer, pull the prescribed literal-quotient Haar measure and level
back through `LeviModel.pointHomeomorph`. The model's actual rational norms
agree with the transported norms by the inverse identity of this homeomorphism.
Apply local VIII.1.2 and then the published injective orbit-pullback finiteness
theorem `finite_discreteSeriesFixedOrbits_of_pullback`. No finiteness premise
on the ambient group or any other Levi is used.

The full fixed set is the sigma set of the already published existential
induced-fixed-orbit sets. Their class-level fixed-vector predicate is already
independent of a representative through normalized-induction equivalences.
Antitonicity follows by quotient induction and fixed-vector antitonicity.
For an actual unitary-orbit member and for the membership criterion at compact
picture levels, use `hasInducedFixedVector_twist_iff` and
`mk_mem_inducedDiscreteSeriesFixedOrbits_iff`, with actual projection continuity,
closedness, compactness, factorization and norm continuity from the imported
`CompactData` and Levi model.

These published transports require `H ≤ d.compact`. They alone do not prove the
arbitrary-level target stated here. That additional target is kept visible and
unproved. The definition at arbitrary `H` uses existence of one orbit member;
no independence theorem is assumed as carrier data. The conditional finiteness
proof in the companion uses this existential form and the separate normal-level
comparison, so it does not assume the arbitrary-level target.

No Fourier support, smoothness, VII.1.4 covariance, synthesis, inversion or
Plancherel theorem is claimed by this module.
