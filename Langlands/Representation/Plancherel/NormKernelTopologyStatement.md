# Topology and compact-subgroup properties of the common norm kernel

Author: Worker 200.

Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.2.3, printed p.106 (PDF p.112), proves that every rational norm character
contains every compact subgroup in its kernel. He then proves that their
common kernel is open, closed and normal, contains all compact subgroups, and
contains the derived group. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Normality of the generic common kernel is already constructed in
`Langlands.Representation.Plancherel.UnramifiedCharacters`.

`CommonNormKernelTopologyStatement` is a derived generic analytic prerequisite
for this passage. It quantifies over a group `G` with a topology,
`NonarchimedeanGroup G`, and `WeaklyLocallyCompactSpace G`, an arbitrary index
type `I` in an independent universe, and a family of positive characters
`ν : I → (G →* ℝ≥0ˣ)`. The only premise on the family is continuity of every
character. The conclusion states that:

- the actual intersection `commonNormKernel ν` is open and closed;
- every subgroup of `G` that is compact as a subset lies in this intersection;
- the abstract group commutator subgroup lies in the intersection.

The index family need not be finite or additively packaged. In particular, the
openness conclusion is not justified by treating an infinite intersection of
open kernels as open. The intended proof first shows that any continuous
positive character is trivial on every compact subgroup, since its image is a
compact subgroup of the positive reals. The published
`Langlands.compactOpenSubgroupBasis` then supplies a compact open subgroup
contained in the intersection, proving openness. Closedness follows from
continuity and the closed identity in the value group; the commutator conclusion
follows from commutativity of the value group. This paragraph describes a proof
route, not a proof furnished by this statement file.

The hypotheses use the generic nonarchimedean-group and local-compactness
interfaces. They do not assert their realization on rational points. To apply
this target to the source, `ν` must be the actual normalized absolute values of
all rational algebraic character evaluations, with continuity and the group
topology supplied by the shared algebraic-group and rational-point programs.
No characteristic, splitness or positive-rank restriction is introduced.

The commutator conclusion concerns the abstract rational-point group when
specialized. It neither identifies this subgroup with the rational points of
the algebraic derived subgroup nor proves containment of all such points.
That separate algebraic evaluation comparison remains required for the full
source assertion. Unimodularity, also stated in Renard’s proposition, is not
part of this target and remains a separate proof obligation.

This file supplies a Prop-valued statement only. Its proof, rational-point
specialization, valuation/image-lattice comparisons, character tori and Haar
normalizations remain separate obligations. Openness, compact-subgroup
containment and the other displayed conclusions are not taken as new structural
hypotheses of the Plancherel program.
