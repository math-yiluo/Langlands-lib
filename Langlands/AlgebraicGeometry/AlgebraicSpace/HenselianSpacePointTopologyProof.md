# Proof of Conrad's Proposition 5.4 (corrected to locally separated spaces)

Authors: Worker 105, Worker 1525.

This module proves `HenselianSpacePointTopologyStatement`: Proposition 5.4 of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed
pp.14–15 (source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`), topological part,
corrected to locally separated spaces as explained in the Markdown of
`HenselianSpacePointTopologyStatement`.

- `henselianSpacePointTopology : HenselianSpacePointTopologyStatement.{u}`, in an
  arbitrary universe `u`. Given a nontrivially normed field `K : Type u` and
  `hK : IsHenselianValuedField K`, the witness family is the étale-chart topology
  `etaleChartTopology K` (module `EtaleChartTopology`): on `RingPoints K X K` it is the
  strongest topology making the map `U(K) → X(K)` continuous for every étale chart
  `U → X` by an actual scheme of finite type over `Spec K`, where `U(K)` carries the
  scheme point topology. The three conjuncts of the statement are the three conjuncts of
  the specialization `etaleChartTopologyAdmissible K hK` of the theorem
  `etaleChartTopologyAdmissible : EtaleChartTopologyAdmissibleStatement`
  (module `EtaleChartTopologyAdmissibleProof`):
  1. admissibility, `IsAdmissibleRationalPointTopology K (etaleChartTopology K)`;
  2. uniqueness: every family `τ'` with `IsAdmissibleRationalPointTopology K τ'` satisfies
     `τ' X = etaleChartTopology K X` for every `X` with
     `IsLocallySeparatedLocallyFiniteType K X`;
  3. the separated-space properties,
     `SeparatedRationalPointTopologyProperties K (etaleChartTopology K)`.

The two statements differ only in that `EtaleChartTopologyAdmissibleStatement` names the
witness topology, while `HenselianSpacePointTopologyStatement` asserts that one exists. No
hypothesis on `K` is used beyond `NontriviallyNormedField K` and
`IsHenselianValuedField K`. The proof uses only the axioms `propext`, `Classical.choice`
and `Quot.sound`.
