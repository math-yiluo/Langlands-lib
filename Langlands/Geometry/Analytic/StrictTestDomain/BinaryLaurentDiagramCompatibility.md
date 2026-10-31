# Elementary compatibility for the binary Laurent comparison

This module supplies elementary derived infrastructure for
`StrictTestDomain.BinaryLaurentDiagramComparisonStatement`. It does not
construct the three comparison equivalences or prove that statement.
The statement and every published dependency remain unchanged.

`relativeRationalEquivOfEq` transports between the actual unit-radius relative
rational quotients when their denominator elements and numerator functions
are equal. The proof eliminates those equalities and uses
`BoundedAlgEquiv.refl`; its forward and inverse maps are therefore bounded.
The accompanying coefficient and fraction laws follow by the same equality
elimination. No equality of distinct presentations is assumed: the two data
equalities are explicit inputs to this elementary transport operation.

For the actual strict upper and lower data, the module computes the actual
intersection arity as four, its denominator as `f`, and its numerator function
as `(f, 1, f², f)` in the existing `finProdFinEquiv` order. The numerator proof
checks all four indices against `RationalIntersection.numerators`.
`laurent_inter_numerator_strictEquiv` then maps this tuple through the inverse
of the existing `strictEquiv`, using preservation of one and powers.

The last two lemmas concern bounded maps, without requiring them to be
equivalences. Given upper and overlap comparison maps with their coefficient
laws, `binaryLaurent_left_square` proves equality of the two composite maps
from the actual strict upper quotient to the relative overlap. It uses
`RationalData.hom_ext` to reduce this equality to coefficients, then the
published `Inclusion.restriction_comp_baseMap`, the two supplied coefficient
laws, and `BinaryLaurent.left_upperBase`. The right square follows by the
same argument with the lower quotient and `right_lowerBase`.

The coefficient laws are hypotheses of these compatibility lemmas only.
They still have to be proved for the constructed equivalences in the
unconditional comparison proof. Neither compatibility lemma supplies or
assumes gluing, exactness or an analytic comparison conclusion.

All results are valid for every complete ultrametric normed field and
presented strict coefficient algebra, including trivial scalar valuations
and zero quotient algebras. The equality transport itself needs no scalar
completeness. No unit-ideal assumption is added: the uniqueness theorem is
applied to the already published rational data, which carry their own
no-common-spectrum-zero condition.

The provenance is internal and derived. The retained original passages
underlying the published diagrams are Achinger, *Introduction to
non-Archimedean Geometry* (November 22, 2020), printed pp.6 and 63–65,
especially Proposition 7.1.1 on p.64, and Berkovich, *Non-Archimedean analytic
spaces*, Trieste lectures (2009), printed pp.8–9, Definition 2.1.6(i) and
Exercise 2.2.2(i)–(iii). Neither source states these concrete Library
transport and compatibility lemmas. The four-variable order is the
Library's own product-numerator convention. The implementation derives all
claims from the published definitions and uniqueness interfaces rather than
from either source's analytic exactness assertion.
