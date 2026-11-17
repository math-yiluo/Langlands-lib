# Geometric inputs for the split semisimple Picard criterion

This module states two geometric inputs for
`SplitSemisimpleSimplyConnectedPicardStatement`. It proves neither input and
makes no claim to prove that final equivalence. All three declarations are
Prop-valued definitions, in every universe `u`.

## Character lifting across a central isogeny

`SplitCentralIsogenyPicardCharacterLiftingStatement.{u}` quantifies over every
field `k : Type u`, connected reductive groups `H` and `G` with split maximal
tori, and a central isogeny `f : H ⟶ G`. If every actual line bundle on
`G.X.left` is isomorphic to its structure sheaf, then

```text
characterRestrict (kernelι f) :
  rationalCharacters H →+ rationalCharacters (kernel f)
```

is surjective. Thus every character of the full scheme-theoretic kernel
extends to a character of `H`. The kernel need not be smooth or reduced.
There is no perfect-field or characteristic assumption.

This is a derived consequence of Milne, *Algebraic Groups* (2017),
Proposition 18.18, printed p. 391 (PDF p. 407), specifically exactness at
`X(Ker f)` in

```text
0 → X(G) → X(H) → X(Ker f) → Pic(G) → Pic(H) → 0.
```

If `Pic(G) = 0`, exactness gives the stated surjectivity. Only this
consequence is encoded: this module does not construct a Picard group,
a connecting homomorphism, or the entire exact sequence. Restriction is
the already published `characterRestrict`, whose value at a character is
composition with the actual inclusion `kernelι f`.

Milne's split condition for reductive groups agrees with
`HasSplitMaximalTorus` by Proposition 21.64, printed p. 443 (PDF p. 459).
His 18.18 requires a multiplicative-type kernel. In this specialization,
the full central kernel is a closed subgroup of a split maximal torus of
`H`: central points centralize that torus, and a maximal torus of a
connected reductive group is self-centralizing (Corollary 17.84).
Closed subgroups of a split torus are diagonalizable (Theorem 12.9(c), printed pp. 233–234, PDF pp. 249–250).
Consequently the source hypothesis is retained, including non-smooth
finite kernels such as roots of unity in positive characteristic.

## A cover with trivial Picard group

`SplitSemisimplePicardTrivialCoverStatement.{u}` quantifies over every field
and every semisimple `G` with a split maximal torus. It asserts the existence
of a semisimple group `H` and a central isogeny `f : H ⟶ G` for which every
line bundle on `H.X.left` is isomorphic to the structure sheaf. It does not
assume or assert simple connectedness of `H`. It does not choose a cover,
assert uniqueness, or impose a universal property.

This specializes Milne, Proposition 18.22 (Iversen's theorem), printed
pp. 392–393 (PDF pp. 408–409). The standing hypothesis in Section 18d is a
split connected group variety; it holds for `G` by semisimplicity and
Proposition 21.64. Proposition 18.22 supplies a multiplicative isogeny
from a connected group variety with trivial Picard group. Such an isogeny
is central by rigidity (Chapter 18, opening paragraph, printed p. 387,
PDF p. 403, citing 12.38). Its source is semisimple when its target is
semisimple, by Lemma 19.14, printed p. 400 (PDF p. 416). These facts give
precisely the `IsSemisimple H` and `IsCentralIsogeny f` clauses. Over a
field these are finite flat surjective isogenies, with local finite
presentation and the actual central scheme-theoretic kernel, as explained
in the existing `CentralIsogeny/Basic.md` and `SimplyConnected/Basic.md`.

Milne obtains 18.22 from the character–Picard sequence, finite generation
of the Picard group of the flag variety (18.21), and projective
representations (18.13–18.16). Those are substantial proof obligations;
the present statement does not discharge them.

## Combined input and intended use

`SplitSemisimplePicardGeometricInputsStatement.{u}` is just the conjunction
of the preceding statements. Its provenance is an internal grouping of
the two derived source consequences.

The intended forward implication uses the cover: simple connectedness
makes `f` invertible, and line bundles transport across the resulting
scheme isomorphism. For the reverse implication, lift a split maximal
torus through an arbitrary central isogeny from a semisimple group.
Character lifting and vanishing of semisimple characters force all
characters of its kernel to vanish. Split-torus characters then detect
that the full kernel is trivial, so the isogeny is an isomorphism. This
paragraph describes a proof route; it is not a proof supplied here.

## Sources and errata

The cited original is registered as `milne-2017-algebraic-groups`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The original passages of 18.18 and 18.22 and their surrounding proofs were
read. The registered official errata snapshot,
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`, was
read in full. Its Chapter 18 entries correct the last sentence of 18.4,
Exercise 18-1, and the target of the map in 18.8; they do not change
18.18 or 18.22. The published target's Markdown gives the detailed
semisimple, split, central-isogeny, and line-bundle convention comparison.
