# Constant pinned charts from the exact affine and normalization theorems

This internal assembly supplies the representation-free constant chart for
arbitrary pairs of affine pinned models and arbitrary common bases. It
retains precisely two mathematical inputs: the exact
`AffinePinnedIsomorphismTheoremStatement` and
`AffinePinnedModel.HasFppfLocalPinnedRepresentatives`. Their unconditional
proofs are not part of this module; the Library proves them as
`affinePinnedIsomorphismTheorem` (in `AffinePinnedIsomorphismTheoremProof`) and
`AffinePinnedModel.hasFppfLocalPinnedRepresentatives` (in
`RelativePinnedComparisonProof`). This module does not assert either input.

`AffinePinnedModel.openPinnedLabelCompleteness` discharges the local
completeness premise of the preceding descent module by applying
`exists_open_comparisonLabel`. Its proof uses the exact affine pinned
theorem through that local classification result.

`AffinePinnedModel.pinnedComparisonChart` takes any models `M,N`, any
common scheme `S` with the two base maps, and any supplied full-centre
relative adjoint quotient of the source pulled-back group. It returns
the actual family

`E : LocalGroupIso (M.groupOver f) (N.groupOver g) (constantParameter S (ComparisonLabel M N))`

together with the bijection, for every relative scheme test `T`,

`(d,b) ↦ (E.refine b).twist innerAction d⁻¹`.

The target is all `LocalGroupIso` families on `T`. Thus the adjoint
coordinate is a point on the original test, and the label coordinate is
an actual morphism from that test to the scheme coproduct of copies of
`S` indexed by the full lattice labels. Locally varying labels on
disconnected tests are included. The label type may be empty or infinite.
No scheme representing isomorphisms is supplied to this construction.

The implemented construction uses `constantPinnedFamily`. The local
completeness theorem plus Zariski and fppf descent classifies every
normalized family uniquely by a morphism into this constant scheme.
The existing natural normalization and full-centre adjoint discrepancy
then give the unique acting point on each original test. The generic
orbit criterion combines the two coordinates into the stated bijection.

`pinnedOuterIsomorphismChart_of_pinnedTheorems` proves the unchanged
`PinnedOuterIsomorphismChartStatement` from the same two inputs. It
classifies this representation-free family in each arbitrary supplied
Isom representative and transfers the orbit bijection. It places no
additional conditions on the supplied quotient or representative.
Nonaffine, disconnected, nonreduced, and empty tests are retained.

The conditional theorem is not an unconditional proof of
`PinnedOuterIsomorphismChartStatement`; the Library proves that statement as
`pinnedOuterIsomorphismChart` in `PinnedOuterIsomorphismChartProof`, by
supplying the two inputs to `pinnedOuterIsomorphismChart_of_pinnedTheorems`.
There is no remaining local-completeness premise in this module.

## Provenance

This is an internal assembly of the full-character-lattice local
classification, actual scheme-coproduct family, descent of morphisms, and
natural pinned normalization. It realizes the derived pair chart from
the split pinned classification argument while keeping the exact affine
and normalization-existence theorem inputs explicit.
