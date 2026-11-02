# Topology of the common kernel of continuous positive characters

Author: Worker 55.

`Langlands.Plancherel.commonNormKernelTopology` proves exactly the published
`Langlands.Plancherel.CommonNormKernelTopologyStatement.{uG,uI}`. It imports the
statement and uses its existing `commonNormKernel` construction unchanged.
The universes of the group and the character index type are independent.

The implemented argument first proves that every compact subgroup `K` lies in
the common kernel. For each index `i`, the published theorem
`Langlands.RankinSelberg.LastRowReduction.eq_one_of_isCompact`, imported from
`Langlands.Topology.CompactNormCharacter`, gives `ν i g = 1` for every `g ∈ K`.
The existing membership equivalence for `commonNormKernel` then gives the
simultaneous inclusion. The imported compact-character theorem uses boundedness
of the real-valued image of `K`: powers exclude values greater than one, and
inverses exclude values less than one.

Next, `Langlands.compactOpenSubgroupBasis`, imported from
`Langlands.Topology.CompactOpen.NeighborhoodBasis`, supplies a compact open
subgroup by taking the identity neighborhood to be the whole group. The
previous inclusion puts this single subgroup in every character kernel at
once. `Subgroup.isOpen_mono` proves that the common kernel is open. This works
for an arbitrary, possibly empty or infinite, index type.

For closedness, the proof rewrites the subgroup intersection as an intersection
of sets. Each set is the equalizer of the continuous character `ν i` and the
constant identity in `ℝ≥0ˣ`, so `isClosed_eq` and `isClosed_iInter` apply.
Only the value group needs its existing separation instance. For the final
inclusion, `Subgroup.commutator_le` reduces to commutator generators.
`map_commutatorElement` maps each generator to a commutator in the commutative
value group, where it equals one.

The provenance is the generic analytic deduction isolated in the statement
Markdown from Renard, *Représentations des groupes réductifs p-adiques*,
French edition of 9 July 2026, V.2.3, printed p.106 / PDF p.112, the lemma
and following proposition. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 55 read and visually checked this page. The implemented proof uses the
published generic compact-character and compact-open-basis results to carry
out the analytic argument with exactly the target hypotheses.

The conclusion concerns the given topological group and continuous positive
characters. Specialization to reductive rational points still requires their
topology and continuity of the actual rational norm characters. Containment
of all points of an algebraic derived subgroup, unimodularity, image lattices
and character tori are separate obligations.
