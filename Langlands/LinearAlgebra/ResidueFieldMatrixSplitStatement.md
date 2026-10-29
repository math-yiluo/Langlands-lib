# Splitting a matrix near an injective residue-field specialization

The declaration
`Langlands.LinearAlgebra.ResidueFieldMatrixSplitStatement.{u}` is a
Prop-valued statement, with no proof supplied in this file.

For every commutative ring `R : Type u`, prime ideal `p`, natural numbers
`m,n`, and matrix `A : Matrix (Fin m) (Fin n) R`, assume that the
specialized column-vector map
`(A.map (algebraMap R p.ResidueField)).mulVec` is injective. The proposition
asserts existence of an element `r ∉ p` and a matrix
`B : Matrix (Fin n) (Fin m) (Localization.Away r)` satisfying

```text
B * A.map (algebraMap R (Localization.Away r)) = 1.
```

The matrix has `m` rows and `n` columns, so `B` is a left inverse for the
localized map from rank `n` to rank `m`; the identity on the right is the
`n × n` identity. The condition `r ∉ p` means the basic open `D(r)` contains
`p`. Both ranks may be zero. The
statement retains arbitrary rings, including rings with nilpotents and
nonnoetherian rings, and the arbitrary carrier universe `u`. It makes no
assertion about one element working simultaneously for different primes.

All objects are existing Mathlib constructions: the actual residue field
of the prime localization, entrywise matrix scalar extension, and the
localization at the powers of `r`. There is no geometric or cohomological
input. A left inverse implies injectivity and remains a left inverse
after every further ring scalar extension; those consequences are not
separate claims of this statement.

## Provenance

This is an internal algebraic strengthening of the matrix step in the
Stacks Project, More on Morphisms, Lemma
`lemma-H1-O-multiple-picard-flat-proper` (tag 0BF2), in its proof at
`more-morphisms.tex` lines 9597–9614, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`. The registered source is
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, folder SHA-256
`b97dd26d238af5bb18d082504515f27f5316b6b87c2a7d68ca8630e7862ad48e`.
Workers 606 and 362 read the complete lemma and proof, lines 9518–9619.
The source uses an injective residue-field matrix to find a maximal
minor nonzero at the prime, and shrinks to make the matrix injective.
For the affine, finite free case here, invert that determinant. The
inverse of the resulting square row minor, composed with row
projection, supplies the stronger left-inverse conclusion. This explains
the specialization and strengthening; it is a proof obligation rather
than a direct quotation of a source theorem.

The retained source README and comment audit were checked. Its recorded
corrections concern typographical errors in tag 0BDP and do not change
the matrix step. No errata file for this registered source was found in
the supplied Library's public notes. Worker 606 authored the statement design for the relative two-axis Picard
argument; Worker 362 adapted its documentation for publication. The statement
is a pure algebra input to that argument and does not assert a geometric
two-axis or cube theorem.
