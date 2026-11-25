# Unequal-rank pointwise factorization from complex place tests and the TC slice comparison

Module `Langlands.Global.RankinSelberg.UnequalPointwiseFactorizationTCReductionStatement`,
namespace `Langlands.Global.RankinSelbergGlobal`. The only declaration is a `Prop`-valued
statement. The field universe `u` and the spectral presentation universe `uQ` are
independent.

## Statement

`UnequalPointwiseFactorizationTCReductionStatement` is the implication from two premises:

1. [`InfiniteWhittakerSliceModelTCStatement`](InfiniteWhittakerSliceModelTCStatement.md)
   gives the normalized local model maps and actual one-place slice equalities
   (`ModelData`) for a single cuspidal realization and its spectral presentation at each
   totally complex field. The comparison concerns one realization at a time. It can be
   applied separately to the rank `r` member with the character and to the rank `t`
   member with the inverse character.
2. `ComplexUnequalPlaceTestsStatement` in
   [`UnequalInfinitePlaceTests`](UnequalInfinitePlaceTests.md) applies at each complex
   place of a number field, with the original hypotheses. It covers ranks `t < r`, actual
   cuspidal realizations and their contragredients, the complex additive component and
   archimedean parameters. It gives one pair of actual complex Whittaker restrictions in
   the two ranks, for the character and its inverse, together with quotient measure data.
   The block-zero test integral and the dual test integral are each holomorphic on a right
   half-plane and nonzero at a point of that half-plane. This is a local existence
   assertion, not a local functional equation.

The conclusion is `UnequalPointwiseFactorizationTCStatement` in
[`UnequalFactorizationAtStatement`](UnequalFactorizationAtStatement.md), unchanged: the
pointwise factorization `UnequalPointwiseFactorizationAt F` at every totally complex
number field `F`. For the data of that proposition it gives vectors spherical outside `S`,
archimedean and finite local data, and a nonzero constant `κ`. With these, the ordinary
global integrand and the dual kernel factor pointwise on the integral quotient classes. The
local functions at `S` integrate to the ordinary and dual test integrals. The four
nonvanishing clauses hold: for the two archimedean products and for the ordinary and dual
local integrals at each place of `S`. The real-place index occurs in the conclusion but is
empty at these fields. There is no real-place test premise and no premise about fields
with a real place, apart from the field quantifier of the complex test statement.

## Provenance and proof boundary

This is the unequal-rank counterpart of the equal-rank totally complex pointwise
reduction `EqualPointwiseFactorizationTCReductionStatement`. The Library's `unequalPointwiseOfInfiniteTests` in
[`UnequalInfiniteWhittakerReduction`](UnequalInfiniteWhittakerReduction.md) derives the
unrestricted pointwise factorization from the joint archimedean test
`UnequalInfiniteWhittakerTestStatement`. That argument applies its joint test only at the
field of its conclusion. The intended proof fixes a totally complex `F`. It applies the
slice comparison at `F` to both members of the pair and the complex place tests at the
complex places of `F`, and handles the real places by eliminating the empty index. It thus
assembles the joint archimedean test at `F` and passes it to the same-field form of the
pointwise argument. The Library's unrestricted reductions cannot be applied
directly to the restricted hypotheses here. None of their types, and no unrestricted
target, is changed.

This is a proof target, not a proof of the implication or of either premise. It neither
integrates the pointwise formulas nor proves a local or global functional equation. The
same-field integration target `UnequalArchimedeanFactorizationAtReductionStatement` can
consume its conclusion at each totally complex field.

**Source.** J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in J. Bernstein and
S. Gelbart (eds.), *An Introduction to the Langlands Program*, Birkhäuser, 2004,
pp. 197–228, `cogdell-2004-analytic-theory-gln`. §1.2, printed pp. 201–202 (PDF pp.
204–205), gives the factorization of pure-tensor Whittaker functions. The proof of
Theorem 4.1, printed pp. 219–220 (PDF pp. 222–223), gives the unequal-rank product
expressions for factorizable data. The split of the Lean statements into pointwise and
integrated forms, the actual comparison and test hypotheses, and the restriction by field
signature are derived Library interfaces, not separate assertions of Cogdell.
