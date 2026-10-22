# CM types on actual complex embeddings

This construction concerns a number field `K : Type u` with Mathlib's `Field`,
`NumberField`, and `NumberField.IsCMField` instances. A `CMType K` is a subset of
the actual ring embeddings `K →+* ℂ` containing exactly one of each embedding
and its complex conjugate. These finite sets and their subtypes have no chosen
topology. A CM type is additional data, not an isomorphism class of fields or
an assertion that a global character exists.

`conjugate` takes the complementary type. `equivInfinitePlace` identifies the
selected embeddings with Mathlib's actual infinite places, and `embedding`
selects the unique member above a given place. The file proves existence and
uniqueness, the cardinality formula, and twice that cardinality equals the
degree of the number field over the rationals. `ofSection` constructs a CM type
from any actual section of embeddings over infinite places. `canonical` applies
this to Mathlib's chosen place embeddings, providing an actual inhabitant.

`induce Φ ι` is the set of all complex embeddings whose restriction along
`ι : F →+* K` belongs to `Φ`. The conjugate-pair condition, compatibility with
conjugation, and compatibility with composition are proved. For an imaginary
quadratic field `F`, with its quadratic-degree instance over `ℚ`,
`ofImaginaryQuadratic τ` is the singleton consisting of the specified embedding
`τ`. Its validity is proved from the degree and the absence of real places.
Consequently `inducedFromImaginaryQuadratic ι τ` consists **exactly** of embeddings
`σ` satisfying `σ.comp ι = τ`; this condition is not replaced by an arbitrary
choice of representatives.

For an actual totally real number field `E` with an algebra structure on `K`
and `[IsQuadraticExtension E K]`, `realPlaceEquiv` proves that restriction of
infinite places is a bijection. Surjectivity comes from Mathlib's extension
of field embeddings, and injectivity is deduced using the proven number of
places and the quadratic degree. `embeddingAbove Φ E τ`, for a real embedding
`τ : E →+* ℝ`, is the unique selected embedding of `K` restricting to
`Complex.ofRealHom.comp τ`. The constructed family for the induced imaginary
quadratic type therefore simultaneously has the prescribed restrictions to
both fields. No compatibility hypothesis about arbitrary completion charts
is used to obtain these restrictions.

The implementation uses explicit universes `u`, `v`, and `w` for the fields.
The coefficients and embedding target are the ordinary complex field; there
is no scalar transport to an algebraic closure or a nonarchimedean coefficient
field. The proofs of the conjugate-pair property, inverse/uniqueness properties,
restriction identities and cardinalities are intrinsic to the constructions.

## Source and implementation correspondence

Michael Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39 (1999), 299–318:

- Section 1, printed p.301 (one-based PDF page 3), fixes a totally real field and
  a totally imaginary quadratic extension.
- Section 4, printed p.308 (PDF page 10), chooses the CM type consisting of all
  complex embeddings inducing a specified complex embedding of an imaginary
  quadratic subfield. This is exactly the membership predicate of
  `inducedFromImaginaryQuadratic`.
- The continuation on pp.308–309 includes additional hypotheses and geometric
  constructions. Those are not part of this embedding-selection construction.

The retained original has source ID
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d` and SHA256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
Original PDF pages 1–3 and 10–11 were read directly for this group.

The reusable general CM-type operations and selected-embedding equivalences
are derived construction details for that source convention. They use pinned
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, specifically
`NumberTheory/NumberField/CMField.lean` and
`InfinitePlace/{Basic,Embeddings,Ramification,TotallyRealComplex}.lean`:
actual CM fields, complex conjugation, embedding fibers, extension of
embeddings, and number-field degree/place formulas.

This file does not identify a reflex field, construct a prime selected by a
complex-to-adic embedding, prove splitting at a rational prime, or choose a
Shimura datum. It does not construct a Hecke character with this type, prove
global conjugate self-duality, or supply compatible completion charts.
Those constructions and theorems remain separate obligations.
