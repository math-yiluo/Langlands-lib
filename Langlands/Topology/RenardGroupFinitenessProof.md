# Renard II.3.2: proofs for actual coset quotients

This module proves the unchanged published proposition
`Langlands.Topology.RenardGroupFinitenessStatements.Assertions.{u}` by the
universe-polymorphic theorem
`Langlands.Topology.RenardGroupFinitenessProof.assertions`. The three component
theorems prove its conjuncts in their original order. The statement module and
all its prerequisites are imported unchanged.

The original source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.3.2, “Un résultat de finitude,”
the entire lemma and proof on printed page 43 / PDF page 49. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 1218 read that page and the supplementary 2010-edition errata PDF pages
2–3 (source `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`).
The latter's page 3 distinguishes sigma-compactness from the other
countability properties; the governing source remains the 2026 book. The
statement pair records the source's t.d.-space convention and its topology.

## Scope and carriers

Every component quantifies over `G : Type u` with its supplied group, topology,
and topological-group instances, and retains the hypothesis
`Langlands.Topology.IsLocallyProfinite G`. Compactness and openness are
properties of the actual subgroup sets in this topology. Only the countability
component quantifies over `[SigmaCompactSpace G]`. There are no added
hypotheses, and no restriction on the universe `u`.

The relative carrier is literally `K1 ⧸ K.subgroupOf K1`; `K1` has its induced
subtype topology. The retained hypothesis `K ≤ K1` identifies the subgroup
`K.subgroupOf K1` with `K` inside `K1`. The ambient carrier is literally
`G ⧸ K`, the quotient by `QuotientGroup.leftRel K`. Its relation
`x⁻¹ * y ∈ K` has classes `gK`, as used in Renard's proof. Both quotients use
the existing ordinary quotient topology, coinduced by their quotient
projections. No normality or quotient-group structure is needed.

## Implemented Lean arguments

`relativeQuotientFinite` converts `IsCompact (K1 : Set G)` into a local
`CompactSpace K1` instance via `isCompact_iff_compactSpace.mp`. The theorem
`Subgroup.subgroupOf_isOpen K1 K hKopen` expresses that membership in `K`,
restricted to `K1`, is open in the subtype topology. Applying
`Subgroup.quotient_finite_of_isOpen` to this relative subgroup proves
`Finite (K1 ⧸ K.subgroupOf K1)`. That Mathlib theorem uses discreteness from
openness, compactness of the quotient as a continuous quotient of the compact
space `K1`, and `finite_of_compact_of_discrete`. Thus the implemented route is
through compact discrete spaces. Renard instead extracts a finite subcover
from the disjoint open coset cover of `K1`.

`quotientDiscrete` applies `QuotientGroup.discreteTopology hKopen` directly to
the supplied topology and subgroup. This theorem proves that the existing
quotient topology is discrete. The resulting discreteness proof is an output;
it does not replace that topology.

`quotientCountable` obtains the same discreteness proof as a local typeclass
instance for `G ⧸ K`, then applies `countable_of_Lindelof_of_discrete`.
Instance inference obtains `LindelofSpace G` from `[SigmaCompactSpace G]`;
the proof explicitly installs `Quotient.lindelofSpace` as a local instance of
`LindelofSpace (G ⧸ K)`. The latter uses the
continuous surjective quotient projection. A discrete Lindelöf space is
countable, giving the required `Countable` instance for the actual quotient
carrier. Renard instead extracts finitely many cosets over each compact set
in a countable compact cover. These are different implementations of the
same source assertion; the Lean proof requires no second countability.

Some retained source hypotheses are unused by these stronger general topology
results. Relative finiteness uses compactness of `K1` and openness of `K`;
discreteness uses openness of `K`; countability additionally uses
sigma-compactness of `G`. In particular, neither local profiniteness nor
normality is used to manufacture any of the conclusions. All hypotheses of
the published propositions remain in the exact theorem types, including
compactness and openness of both nested subgroups and their nesting.

Finally, `assertions` packages the three component proofs as the exact closed
aggregate, without an additional parameter or assumption.

## Dependencies and provenance

The proof is an application of existing results in the pinned Mathlib, rather
than a port of their implementations. The direct sources are Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`:

- `Mathlib/Topology/Algebra/OpenSubgroup.lean`,
  `Subgroup.subgroupOf_isOpen` and `Subgroup.quotient_finite_of_isOpen`
  (lines 304–318); registered source `mathlib-open-subgroup-5ed296525643`,
  SHA256 `ae99f92e86fbbcf2301be8e78ef84dd31a498b29cf11b915b1ce2494c7e9395c`.
- `Mathlib/Topology/Algebra/Group/Quotient.lean`, quotient topology and compact
  quotient instances (lines 30–38), `QuotientGroup.discreteTopology_iff` and
  `QuotientGroup.discreteTopology` (lines 88–117); registered source
  `mathlib-group-quotient-topology-5ed296525643`, SHA256
  `b5180e0926ca4efc8027602e5e7fb68f7a8f3a034f5b7e748193efa9944597b0`.
- `Mathlib/Topology/Compactness/Lindelof.lean`, sigma-compact-to-Lindelöf
  instance (lines 532–533), `countable_of_Lindelof_of_discrete`
  (lines 571–572), and `Quotient.lindelofSpace` (lines 679–685); registered
  source `mathlib-lindelof-5ed296525643`, SHA256
  `e75a097a0ac483a700c8eb13d91246dd151d3e34edf331f8fcb4f4f15fbe505d`.

The Lean environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0.
No new definition of a coset carrier, topology, group structure, or source
statement is introduced.
