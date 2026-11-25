# Statement: reduction of connected-group unirationality

`Langlands.GroupScheme.ConnectedGroupUnirationalityReductionStatement.{u}`
is the following proposition-valued definition:

```lean
TorusUnirationalityStatement.{u} →
  SplitUnipotentAffineSpaceStatement.{u} →
    ConnectedGroupUnirationalityStatement.{u}
```

This is an internal reduction between three published Library statements.
It adds no hypotheses to any of those statements and does not itself prove
the implication or its two premises.

The first premise asserts rationality of Weil-restricted multiplicative
groups for finite field extensions and finite étale algebras, and
unirationality of every torus over every field. The second premise
identifies an affine group with a split unipotent series of length `n`
with affine `n`-space as a scheme over its field. The conclusion asserts
unirationality of every smooth connected affine group over a perfect
field and of every connected reductive group over an arbitrary field.
All three statements use the same universe `u`; the reduction imposes
no infinite-field restriction.

The intended proof uses the torus premise for infinite-field reductive
groups through torus domination. For finite fields, quasi-splitness
and an open three-factor cell reduce reductive unirationality to the
two premises and product unirationality. Over a perfect field, the
unipotent-radical quotient is reductive, and the split radical has a
scheme section over the affine quotient. The resulting multiplication
map from radical times quotient is surjective.

The reduction is derived content authored for the Library, rather than
a statement quoted verbatim from the literature. Its mathematical
motivation is Milne, *Algebraic Groups* (2017), Theorem 17.93
(printed p.382), Remark 17.94(a) (printed p.382), Proposition 12.64
(printed p.251), and 14.66 (printed p.299), registered source
`milne-2017-algebraic-groups`. The registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to
17.93 or 17.94. A proof of this reduction remains separate from the
independent proofs of its premises and from the unconditional target.
