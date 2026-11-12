# Exactness of compact-open fixed vectors

Author: Worker 136. The theorem `Langlands.Hecke.fixedVectorsExact` proves exactly
`Langlands.Hecke.FixedVectorsExactStatement.{u,v}` with independent universes.
It is Proposition (iv) of Renard III.1.5.

The original source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, printed pp.60–61 / PDF pp.66–67, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 136 read these two PDF pages. Renard refers to exactness of the idempotent
functor in I.3.1; the implemented proof instead uses the published finite-orbit
averaging map, which requires no measure on the group.

Suppose the range of `f` is the kernel of `g`. A fixed vector in the image of the
restricted `f` is killed by the restricted `g`, by the original range-kernel equality.
Conversely, a fixed vector `y` killed by `g` has some preimage `x` under `f`.
Average `x` over the compact open subgroup using `Compact.averageMap`. Its value is
fixed, and naturality `Compact.averageMap_commute` shows that its image is the
average of `y`. The identity `Compact.averageMap_id` makes that image exactly `y`.

The imports are the unchanged target statement module and
`Langlands.Representation.Compact.ProjectionProof`, which supplies fixedness,
naturality and the identity on fixed vectors. No hypotheses or conclusions are added
to the published statement.
