# Actual irreducible realizations of integral generator images

Authors: Worker 585 (construction and proofs), with Worker 76 (the surrounding
fixed-factor-vector strategy).

This internal construction transports an endomorphism of the actual exact
finite-length smooth Grothendieck group to genuine irreducible coefficients.
It proves that an actual irreducible embedding occurs in the target factor
vector and turns a signed generator image into an actual irreducible output.
It also proves the required Aubert image assertion in rank zero. The general
positive-rank Aubert irreducible-image theorem is still an obligation.

## Exact coefficients and operator transport

For any field `k : Type uR`, group `G : Type uG` with a topology, and independent
representation-carrier universe `uV`,
`SmoothRep.IrreducibleOperator.onIrreducibles D` is the composite

```text
irreducible lattice --realizeIrreducibles--> exact finite-length K0
                   --D--> exact finite-length K0
                   --factorMap--> irreducible lattice.
```

The labels are the existing genuine isomorphism classes of actual irreducible
smooth representations. The group is the existing quotient by every actual
short exact sequence, including nonsplit sequences. Neither construction is
replaced. The two inverse identities already proved in
`Smooth.IrreducibleGrothendieckProof` show that realizing the transported
operator gives `D` on realized classes and that transport on a factor vector
agrees with applying `factorMap` after `D`.

These identities transfer injectivity, involutivity and fixed classes to
irreducible coefficients under the explicit corresponding hypotheses on `D`.
They do not assert any such property for an arbitrary endomorphism or prove
involutivity of the Aubert operator.

## An actual embedding occurs in the factor support

`compositionFactors_effective` proves nonnegativity of every coordinate of an
actual finite-length object's factor vector. Every label has an actual
irreducible representative, and its coordinate is the natural-valued
composition multiplicity, cast to an integer.

`compositionMultiplicity_self` compares the published coordinate formula with
the published single-generator formula for an irreducible object. Its own
multiplicity is one. For an actual injective intertwiner `A -> B`, with `A`
irreducible and `B` of finite group-algebra length,
`compositionFactors_pos_of_injective` then applies the published
`jordanHolderInjectiveMonotonicity` to the chosen actual series of both objects.
The multiplicity in `B` is at least one, so its integer coordinate is positive.
`mem_support_compositionFactors_of_injective` records the resulting support
membership.

The imported monotonicity proof uses the actual quotient of `B` by the
intertwiner's invariant range, actual short exact decomposition and
Jordan–Hölder independence. No splitting or vector-space finite dimension is
required here, and the finite-length proof for `A` follows from irreducibility.

## Actual output from a signed generator

`exists_irreducible_image_of_signed_generator` assumes precisely that the
transported image of the input label is a genuine irreducible generator or its
negative. It selects an actual irreducible representative of the output
label, applies realization to the coefficient equality and uses the inverse
identities and the generator formula. The result is an equality up to sign of
the original actual exact classes. Both finite-length witnesses are supplied
by `hasFiniteLength_of_isIrreducible`.

`exists_irreducible_image_of_sign_adjusted_generator` instead accepts a
generator image for `onIrreducibles (s • D)`, where the explicitly supplied
integer `s` is either `1` or `-1`. Realization yields the actual class equality
for `s • D`; removing that sign gives the disjunction for `D`. This is a
conditional algebraic adapter. It establishes no signed effectivity or
generator-image input for the Aubert operator.

## Rank zero and conventions

`Aubert.irreducibleImage_rankZero.{uF,uV}` is unconditional. It installs the
supplied topology of an arbitrary `PadicField.{uF} p`, retains carriers in
`Type (max uF uV)`, and chooses the input actual irreducible representation
as its output. The published `alternatingOperator_rankZero` says that the
existing unadjusted operator is identity on the exact group in rank zero.
The positive equality follows immediately, with finite length derived from
irreducibility.

This uses the actual rank-zero induction and coinvariant equivalences already
proved in `Aubert.RankZero`. It retains the existing upper block normalized
induction and Jacquet maps, positive half modulus and right translation. No
new functor, sign convention, carrier resizing or hypothesis is introduced.

## Provenance and scope

All new content is derived internal algebra from the published actual
Jordan–Hölder, exact-K0, irreducible-realization and rank-zero theorems. No new
literature statement is transcribed. The corrected complex, its two-sided
Bruhat support and terminal homology, signed effectivity in positive rank,
the quasicuspidal induction eigenvalue and the remaining formal duality
identities are outside the claims of this module. The original Aubert
Proposition 3.2 and its withdrawn proof are not used.

The module imports the existing irreducible-image proposition only as the
specification for the surrounding task. It leaves that pair and every pair it
imports unchanged. No analytic segment, multisegment, strong-head, tempered,
square-integrable or regular classification result is an input.
