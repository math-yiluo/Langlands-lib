# The Hausdorff criterion from the actual affine-line origin

This target formalizes the necessity observation in the paragraph immediately
after Proposition 2.1 on printed page 2 of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The sufficiency direction is the closed-embedding conclusion of Proposition
2.1 on the same page.

Let R be an arbitrary commutative ring and S a commutative R-algebra, in the
common scheme universe. S has a specified topology making it a topological
ring. R needs no topology. Actual relative S-valued points are morphisms
from Spec S in the category of schemes over Spec R. The paper's same-ring
setting is obtained by taking S = R with its identity algebra structure.
The separate value-algebra formulation is a derived generalization: the
origin still has exactly zero as its coordinate image, and the topology
argument takes place in the additive topological group of S.

`AffineSchemeTopologyClosedEmbeddings R S T` means that every actual closed
immersion between finite-type affine schemes over Spec R induces a closed
embedding of the actual S-point spaces with the assigned topologies T.
The binders require affine source and target with locally finite-type
structure morphisms; for these affine schemes this is the full finite-type
condition. This strengthens the existing closed-immersion axiom, which
requires only an embedding.

`AffineSchemeHausdorffCriterion R S` is the following conjunction.

1. For every topology assignment T normalized on the actual affine line by
   its coordinate evaluation homeomorphism, the range of the actual origin
   map on S-points is closed in that assigned affine-line topology if and
   only if S is Hausdorff.
2. Every such line-normalized assignment that sends all actual finite-type
   affine closed immersions to closed embeddings forces S to be Hausdorff.
3. For the independently defined global-section evaluation topology
   assignment, sending all those closed immersions to closed embeddings is
   equivalent to S being Hausdorff.

The first clause uses `affineLineOrigin R`, the actual morphism induced by
evaluation R[t] → R at zero, rather than an abstract singleton map. Its image
on points has already been identified with the zero-coordinate locus. The
second clause tests the strengthened requirement on this closed immersion.
The third clause uses the canonical evaluation assignment on both source
and target spaces, without defining that topology through a desired property.

The necessity clauses need only line normalization among the four axioms:
continuity of addition and negation in S is already part of the explicit
topological-ring hypothesis. Thus the target also implies the source claim
for assignments satisfying all four axioms. It imposes no Hausdorffness,
nontriviality, locality, open-unit, local-compactness or faithfulness premise.
It makes no assertion about a topology assignment lacking line normalization.
These are proposition definitions; their proof is a separate contribution.
