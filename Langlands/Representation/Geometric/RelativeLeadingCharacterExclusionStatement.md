# Leading real-character exclusion on an actual reversed geometric piece

Authors: Worker 526, with the geometric extraction and chamber design of
Worker 828 and the relative-comparison coordinate guidance of Workers 359
and 430.

`Langlands.GLRelativeGeometricLeadingCharacterExclusionStatement.{uF,uV}`
is an internal proposition definition. This pair states the interface;
it supplies no proof. Field and source-carrier universes remain independent.

The proposition quantifies an actual finite p-adic extension `F`, compatible
data `T`, every rank `n`, and every positive ordered block shape `B` of that
rank. For the actual product-Levi topology it takes one Borel Haar measure
on `B.Levi F.Carrier` modulo its full center, an actual smooth complex
representation `A` of this Levi, and `IsTemperedModCenter A.representation`
for that supplied measure. This analytic property includes admissibility.
There is no irreducibility or support assumption on `A`.

For every strictly decreasing real vector `t`, every actual minimal
representative `v` from `B` to `B.reverse`, and source and target
refinements `S` and `R`, the hypotheses include the actual equalities

```text
sourceLevi F.Carrier B B.reverse v = refinedLevi F.Carrier B S
sourceLevi F.Carrier B.reverse B v^-1 = refinedLevi F.Carrier B.reverse R.
```

The source `At` of the piece is the actual coarse real determinant twist of
`A`; the published open-kernel twist law supplies its smoothness. The piece
is exactly `(geometricPieceFunctor T B B.reverse v S R hS hR).obj At`.
For every character `chi` of the target coarse scalar tuple group, assume
that `chi` is a uniform generalized eigencharacter of that actual piece
restricted along `B.reverse.blockScalarLevi F.Carrier`, and that its real
part is

```text
j ↦ (B.reverse.size j : real) * t (j.rev).
```

The conclusion is the exact permutation equality
`v = B.reversePermutation.symm`. The raw geometric index `v` is distinguished
from `u = B.reversePermutation * v`; this conclusion is equivalent to
`u = 1`. No involutivity of block reversal or minimality of `u` from `B`
to `B` is assumed.

The character occurrence uses the public `IsGeneralizedEigencharacter`:
one nonzero vector is killed by a single finite power of every difference
operator. The power is uniform over all scalar tuples. The statement has
no open-kernel premise on `chi`, prescribed full fine character, ordinary
eigenvector premise, scalar-action assumption, chosen comparison,
semisimplicity, finite representation-carrier dimension, filtration premise
or positive-rank restriction. The scalar real coordinates include the
actual target block sizes. Rank zero, one-block shapes and arbitrary real
central shifts of `t` are included.

## Internal derivation and publication boundary

This is an internal derived interface for the relative Hom-comparison
investigation, not a literal transcription of a numbered literature result.
The actual functors retain their published inverse source Jacquet half,
inverse intersection conjugation and positive target induction half.
There is no freely supplied normalization character.

The private implemented route has four steps, which remain separate proof
obligations for a public proof of this proposition:

1. Evaluate an actual induced generalized eigenfunction at a nonzero value.
   On target coarse scalars, centrality and the proved trivial half modulus
   reflect the character to the actual source refined Jacquet action along
   inverse-conjugated coarse scalars. Chamber coordinates identify the
   actual scalar-tuple restriction.
2. Use the actual normalized quotient equivalence for the coarse real
   twist to remove the source twist. In a finite-dimensional fixed space
   supplied by admissibility, extract a genuine open-kernel fine character
   extending the resulting restricted character. The entire carrier is not
   assumed finite-dimensional, and no dual functional is extended
   equivariantly. Restore the source twist on characters to derive the
   actual real-part projection.
3. An upper tempered-exponent cone gives the closed positive root cone
   for the fine real coordinates, divided by positive fine block sizes and
   repeated on diagonal coordinates in each original source block.
4. The actual projection gives the coarse sums of that diagonal vector
   plus the source coarse twist after the inverse permutation. Reversing
   target block labels gives the raw reversed rigidity hypotheses. The
   energy argument and uniqueness of minimal representatives force the
   inverse block reversal.

The private composition compiles, but includes upstream drafts and pending
statements/proofs. This pair imports only public definitions needed to state
its exact actual objects. It does not import or treat those drafts as
accepted mathematics and does not claim a public proof. A future exact
proof must use their independently accepted public declarations.

This interface excludes the leading real part in nonidentity actual pieces.
It does not produce a geometric filtration, identify the identity piece,
construct a generalized real-block projector, isolate the whole induction,
compare arbitrary quotients, factor a fine Hom, or prove the parent Hom
comparison. The same normalization, open-kernel and source-twist boundaries
must be retained in that later work.
