# Proof of the PQ support filtration comparisons, including the identity piece

Author: Worker 154. Module
`Langlands.Representation.Intertwining.PQIdentitySupportProof`.

The theorem
`Langlands.Aubert.General.RepresentedParabolic.pqSupportGraded`
has exactly the published type `PQSupportGradedStatement.{u,v}`. It proves
all three support inclusions, both natural support-subquotient comparisons,
and the natural equivariant identification of the identity support
subquotient with the original smooth representation. The field/group
universe `u` and representation-carrier universe `v` are independent.
No hypothesis is added to the original proposition.

## Source and implemented route

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, VII.3.1–VII.3.2, printed pp.232–233 / PDF
pp.238–239. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 154 read both PDF pages. The proof follows the published target's
derived formulation for arbitrary represented parabolics with common
Levi embedding, rather than restricting to a standard family.

The inclusion and geometric-comparison clauses use `pqSupportComparisons`
from the companion `PQSupportOrbit` module. Its paired Markdown explains
the actual open-support pairs, compact orbit restriction and section
extension, exact normalized target coinvariants, and the published local
normalized geometric comparison. The present module completes the identity
clause by constructing an intersection datum at the actual identity point
and proving its piece naturally equivalent to the original representation.

## A Bruhat-refining order

`Geometric.OrderedDoubleCosets.bruhatLE_index_antitone` proves that every
open-prefix orbit enumeration reverses orbit-closure containment. Suppose
an orbit in the closure of a second orbit occurred earlier. The open
prefix ending just before the second orbit contains the first and misses
the second. Its closed complement contains the second orbit and hence its
closure, a contradiction. This is proved on the actual inducing quotient,
using its quotient map from the ambient group.

`bruhatLinearOrder` transfers the reversed finite index order to the actual
double-coset quotient. `isBruhatRefinement_bruhatLinearOrder` records the
refinement. In the final proof, the published full represented geometric
lemma supplies finiteness; the proved finite closed-subgroup orbit-ordering
theorem supplies an open-prefix enumeration. Thus no order or enumeration
is an extra premise of `pqSupportGraded`.

## The identity intersection piece

For any supplied intersection datum `D` at `z = 1` with the original common
Levi equality `l ≫ p = lQ ≫ q`, `isIso_source_at_one` proves that `D.p'`
is an isomorphism. The datum's scheme-level source intersection identity,
combined with the monomorphism `M → G`, identifies its range inside `M`
with the preimage of `Q`. Every test point of `M` belongs to that preimage
because the same Levi embeds into `Q`. Hence that range is the full subgroup
functor, which makes the closed inclusion an isomorphism.

The published full-intersection results then show that both inner
parabolics and their Levis are full. `leviConjugation_at_one` proves that
the induced automorphism of `M` is the identity: its composite into `G`
is conjugation by 1, and the original Levi embedding is a monomorphism.

`identityPieceEquiv` takes the published `D.leviPieceEquiv`. That linear
equivalence evaluates at 1 in the full inner parabolic induction and then
identifies the Jacquet quotient by the trivial radical with the source.
The existing action formula, together with the identity conjugation just
proved, makes it equivariant for the original `M(F)` action.

`identityPieceEquiv_natural` proves naturality for every original smooth
intertwiner. Evaluation at 1 takes the induced map to the original inner
Jacquet map. Every vector in that inner Jacquet module has a quotient
representative; on such a representative the trivial-radical quotient
equivalence and its compatibility with the original map are definitional.
There is no choice of an unrelated objectwise equivalence.

## Constructing the datum and assembling the exact target

The published parabolic-dynamic theorem implies that the original rational
Levi contains a maximal split torus of `G`; this is
`ParabolicLeviTorus.exists_maximalSplitTorus_factor`. The same torus factors
through both original Levi embeddings by their given equality. Applying
`geometricLemmaIntersectionDatumOfTorusFactors` at `z = 1` therefore
constructs a full intersection datum, including all six subgroup-functor
identities, the original conjugation isomorphism, the point homeomorphism
and the ambient maximal split torus.

Apply `pqSupportComparisons` to a Bruhat-refining order. At the identity,
its first isomorphism compares the total-order quotient with the
closure/boundary quotient, and its second identifies the total-order
quotient with this constructed datum's piece. Their composite gives a
natural isomorphism from the original closure/boundary quotient to that
piece. At each smooth representation, compose its equivariant component
with `identityPieceEquiv`. Naturality follows from the natural isomorphism
and `identityPieceEquiv_natural`, yielding precisely the final quantified
equation in `PQSupportGradedStatement`.

The theorem keeps every original target object, universe and hypothesis.
It uses neither the unproved PQ regularity lemma nor a supplied identity
subquotient identification. The statement's Lean/Markdown pair and its
imported closure are unchanged. The `PQSupportOrbit` helper pair is included
as a repository dependency because it was staged separately and is not in
the workspace's recorded public base.

The successful declaration inspection reports only `propext`,
`Classical.choice` and `Quot.sound` as axioms. Compilation is development
evidence; exact-target validation and independent semantic review are
required for publication.
