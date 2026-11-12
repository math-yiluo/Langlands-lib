# Actual ordered geometric filtrations for maximal standard source Levis

Author: Worker 124.

This module states the remaining filtration input for the rank-one geometric
Jacquet computation. It does not prove its existence. The statement is stronger
than the desired cuspidal computation in that the inducing smooth object is
arbitrary and the maximal source need not be self-associated. The scope is
limited to maximal standard sources and proper standard targets.

## The actual filtration datum

`PointGeometricObjectFiltration i ν hG hi hν hStandard hM hU actual I J σ`
is a structure of actual data, not an existence hypothesis built into the
geometric-term functor. It contains a natural number `tailLength`, a bijection
from `Fin (tailLength + 1)` onto the actual `minimalReps actual I J`, a torus
normalizer lift at each index with its exact quotient-class equation, and
actual source and target geometric semidirect decompositions at those lifts.
The filtration is of the original object

```text
pointInducedJacquetObject i ν hG hi hν hStandard hU I J σ
  = r_I(i_J σ).
```

This uses exactly the actual normalized induction and Jacquet functors; no
Grothendieck group or finite-length functor replaces them. Each actual grade
has a representation isomorphism to the underlying `Rep` of the actual
`geometricTermFunctor` at the same lift and decomposition witnesses. The term
is source intersection Jacquet restriction, inverse-pullback conjugation, then
target intersection induction, with the existing normalized functors.

For a self composite (`I = J`), `identity_last` requires that the final grade
has Weyl class `1`. No full length order is asserted for the other grades.
The length is positive because every minimal-representative set contains the
identity; this does not require a nonempty simple-root type. The datum can
exist even when some or all graded objects are zero.

## The universal proposition

`RationalMaximalSourceGeometricFiltrationStatement.{u,v}` is Prop-valued. It
quantifies the same field, connected reductive group scheme, maximal split
torus, generic cocharacter, canonical `pointTopology`, local compactness,
nonarchimedean structure, Hausdorffness, relative-root and Coxeter data and
visible structural premises as `RationalRankOneGeometricJacquetStatement`.
It retains `StandardLeviIntersectionStatement` as `_hInter`, though the datum's
type does not use it. The actual Levi Weyl identification, root-length,
positive-simple-reflection, minimality and associated-subset premises are
retained. The labels are literally `SimpleRoot i ν`. Field universe `u` and
carrier parameter `v` are independent; carriers have universe `max (u + 1) v`.
Positive characteristic, nonsplit and non-quasisplit groups are included.

For each maximal standard source `J`, every smooth `σ` of the actual Levi, and
every proper target `I`, it asserts `Nonempty` of the datum described above.
There is no cuspidality, irreducibility, finite length, admissibility,
reducibility or self-normalization premise. The representatives, their
finiteness and bijection, decomposition data, actual filtration, grade
isomorphisms and self-composite endpoint order are conclusions. An empty
simple-root type has no maximal source, so the universal statement is then
vacuous. No nonemptiness premise is added.

## Original-source correspondence

This is a derived specialization of the normalized geometric lemma and its
support order, not a newly proved instance of that lemma. Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026 version,
VI.5.1, printed pp.161–163 / PDF pp.167–169, states the normalized theorem for
all smooth representations and its reformulation by actual subfunctors. The
orbits are ordered with open initial unions, and the grades are
`i^L_(L∩z⁻¹Pz) ◦ Int(z) ◦ r^M_(M∩zQz⁻¹)`.
For our `r_I i_J`, `P = P_J`, `Q = P_I`, and the orbit representative is
`z = n⁻¹` for the lift `n` in `W_I \ W / W_J`. The resulting source
intersections are `L_J ∩ n⁻¹ P_I n`, `L_J ∩ n⁻¹ L_I n` and
`L_J ∩ n⁻¹ U_I n`; the target intersections are `L_I ∩ n P_J n⁻¹`,
`L_I ∩ n L_J n⁻¹` and `L_I ∩ n U_J n⁻¹`. These are exactly the published
geometric-term definitions. Conjugation transport acts by inverse pullback,
`x ↦ σ(n⁻¹ x n)` on the appropriate source Jacquet module.

For `I = J`, the identity orbit in `P_J \ G` is the singleton coset `P_J`.
It is closed because the actual parabolic is closed. A finite orbit support
filtration can therefore take it last: all other orbits lie in its open
complement. This is the endpoint refinement retained here. Formalizing the
closed orbit and the refined support order remains part of proving this
statement; the preceding explanation is its mathematical provenance.

Casselman, draft of 1 May 1995, §§6.3 and 7.1, supplies the rank-one motivation:
6.3.3–6.3.5 (printed/PDF pp.57–59) describe the intersection terms, normalization
and cuspidal vanishing, while 7.1.1(a) (printed/PDF p.67) gives the resulting
self-dual exact sequence. Casselman's 7.1 discussion assumes irreducibility
and absolute cuspidality; those hypotheses are not imported into this stronger
filtration statement. Renard's general smooth geometric lemma provides that
scope. The module does not claim a proof of Casselman's sequence.

## Relationship to existing work and remaining proof work

`RepresentedGeometricLemmaStatement` has arbitrary represented parabolics and
scheme-level intersection data, but concludes only unordered `IsGluedFrom`.
Its proof and the bridge to the actual standard families remain separate.
An arbitrary unordered filtration does not determine the direction of a
short exact sequence. A reuse proof here must retain or reconstruct the
closed-identity-orbit endpoint from the actual support filtration.
The existing rational orbit and term constructions may also be used, but their
extra point-Bruhat, continuity, compactness and normalized Haar-character
premises must be discharged from this proposition's displayed data.

No geometric lemma, double-coset comparison or normalized orbit identification
is added as an assumption to this statement. Their exact published proofs or
new derivations are still required. This unit preserves the existing broad
represented-geometric-lemma and exact-K0 proof tasks; it isolates a focused
maximal-source, object-level consumer interface. In particular it is not an
exact-K0 expansion or an assertion that a semisimplification splits.
