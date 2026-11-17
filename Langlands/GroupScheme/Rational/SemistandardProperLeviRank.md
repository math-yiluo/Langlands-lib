# The actual induction rank for proper semistandard Levis

Worker 277, Task 7277. This structural statement and its elementary adapters
prepare the rank induction preceding Waldspurger VIII.2. They do not prove
strict rank decrease or any analytic assertion.

## Source and interpretation

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), printed p.321 (PDF p.87), the induction
paragraph preceding VIII.2, uses strictly smaller semisimple rank for the
proper Levis. The detection argument continues on printed pp.321–322.
Registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The present exact structural target makes explicit a prerequisite of that
argument; the article does not prove a new rank comparison there.

The induction parameter is the published `Langlands.GroupScheme.relativeRootRank`,
namely `Module.finrank ℚ (relativeRootSpan i)`, for the actual roots of a
maximal split torus in the actual connected reductive group. It is neither
the full split rank nor an arbitrary rank function. Its agreement with the
number of simple relative roots is the published `relativeSimpleRootBasis`
(theorem imported through `RelativeRankProof`). Nonreduced root systems
and the empty set of simple roots are retained.

## Declarations and implemented elementary arguments

- `semistandardLeviSplitTorus p hj` factors the original torus through
  **any** closed reductive representing model `j : M ⟶ G` of the literal
  all-test subgroup `p.levi`. It uses `IsRepresentedBy.factorHom` and
  `p.torus_le_levi`. Its composite with `j` is the original torus map.
- `isMaximalSplitTorus_semistandardLeviSplitTorus` uses the published
  reflection of maximal splitness through a closed subgroup. No new
  torus-conjugacy hypothesis or model choice occurs in this construction.
- `relativeRootRank_eq_of_maximalSplitTori` proves independence of the
  maximal split torus in one connected reductive group. The published
  `relativeRankIdentity` identifies each full torus rank with the intrinsic
  split rank and decomposes it as relative-root rank plus the intrinsic
  rational-character rank. Equality of the full torus ranks and cancellation
  of the latter summand give the assertion.
- `SemistandardProperLeviRankStatement` is the outstanding exact Prop
  target: for every field, every connected reductive `G`, every maximal
  split torus, every intrinsic semistandard index with `p.parabolic ≠ ⊤`,
  and every closed connected reductive model of its literal Levi, the
  relative-root rank at the constructed lifted torus is strictly less than
  that of `G`. Properness is equality of all-test subgroup functors, not a
  condition only on rational points. No strict decrease is a field of an
  auxiliary chosen model.
- `relativeRootRank_properLevi_lt` transfers the target's conclusion to
  **every** maximal split torus chosen in that Levi using the proved rank
  independence. It has the strict-decrease target as an explicit premise.
- `semistandardParabolic_eq_top_of_rank_zero` and
  `isEmpty_properSemistandard_of_rank_zero` are conditional elementary
  consequences of that same target. They extract the actual closed
  reductive Levi already guaranteed by the intrinsic index and contradict
  a natural number being less than zero. Thus the proper parabolic part
  is empty in relative semisimple rank zero, including groups with a
  positive-dimensional split centre.

## Dependency and scope ledger

| Input | Status and use |
|---|---|
| `SemistandardSpectralIndex` and all-test containment/decomposition | Published definitions of Task 7229; reused without a competing index or model carrier |
| `relativeRootRank`, `relativeRootSpan`, `relativeSimpleRootBasis` | Published actual root constructions and simple-root/rank comparison |
| `relativeRankIdentity` | Published proof; supplies torus independence |
| `IsRepresentedBy.factorHom`, `IsMaximalSplitTorus.of_comp` | Published structural constructions used by the torus lift |
| `SemistandardProperLeviRankStatement` | New unproved structural target, explicit whenever a rank-decrease consequence is used |
| Lower-rank VIII.1.2 finiteness | Not used here; Task 7275 supplies its local predicate and proper-support adapters |
| Lower-rank local synthesis reconstruction | Not used here; Task 7276 supplies its separate local predicate for the actual constant-term Schwartz function |

All field characteristics, nonsplit and non-quasisplit connected reductive
groups and arbitrary field universe `u` are allowed. No representation
carrier occurs in this structural unit; downstream analytic units retain
an independent representation universe. No same-rank finiteness, general
Fourier support, synthesis reconstruction, projection, kernel equality or
Plancherel theorem is assumed or concluded. The global well-founded
assembly remains with Task 3642, and all Task 4534 controls are preserved.
