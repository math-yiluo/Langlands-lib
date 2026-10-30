# Matrix splitting near a prime

This module proves the published proposition
`Langlands.LinearAlgebra.ResidueFieldMatrixSplitStatement.{u}` as
`Langlands.LinearAlgebra.residueFieldMatrixSplit`. For any commutative ring,
prime ideal and rectangular finite matrix whose residue-field column map is
injective, it constructs a left inverse after inverting one element outside
the prime. Both ranks may be zero, and the ring universe is arbitrary.

The private field helper first identifies the matrix rank with the source
dimension using injectivity. Equality of row rank and column rank shows that
the rows span the full coordinate vector space. It chooses a basis from those
rows and reindexes it by `Fin n` using equality of basis cardinalities.
Choosing a row index for each basis vector gives a square row minor whose
rows are linearly independent, hence whose determinant is nonzero.
The same finite-dimensional argument covers dimension zero, without a
positive-rank hypothesis.

The theorem `residueFieldMatrixSplit_of_injective` specializes the helper to
the prime residue field and lifts the chosen minor to the original ring.
It sets `r` to its determinant. Determinant naturality and the fact that the
residue-field map has kernel the prime show `r` is outside the prime.
In `Localization.Away r`, the square minor `C` has unit determinant. Let `E`
be the matrix selecting the chosen rows, so `E * A_localized = C`.
Then `C⁻¹ * E` is a left inverse for `A_localized`, by associativity and
Mathlib's nonsingular-inverse identity. The final theorem packages the
expanded assertion into exactly the published Prop-valued target.

This is an internal finite linear algebra proof of the strengthening
described in the statement. The motivating original is the Stacks Project,
More on Morphisms, Lemma `lemma-H1-O-multiple-picard-flat-proper` (tag 0BF2),
complete lemma and proof at `more-morphisms.tex` lines 9518–9619, especially
9597–9614, commit `a04446e57ec1fbc252a871afcec7752fb2807b14`.
The registered source is `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`,
folder SHA-256 `b97dd26d238af5bb18d082504515f27f5316b6b87c2a7d68ca8630e7862ad48e`.
The source obtains neighbourhood injectivity from a maximal minor nonzero
in the residue field. The affine finite free argument above gives the
stronger left inverse by inverting the determinant and composing the inverse
minor with row projection. The retained source README and comment audit were
checked; its recorded typographical corrections concern tag 0BDP and do not
change this step. No corresponding project erratum was found.

Worker 606 authored the original proof prototype and this adaptation. The
proof has no geometric input and discharges no two-axis, perfect base-change
or relative cube theorem.
