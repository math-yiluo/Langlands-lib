# Geometric steps in unramified zero descent

This module proves
`UnramifiedZeroDescentGeometricReductionStatement`: valuation-apartment
existence, apartment-compatible unramified descent, and the zero-group
action without inversions on upstairs facets imply clause 3 of
`UnramifiedZeroDescentStatement`. All three inputs remain hypotheses.
The conclusion covers every upstairs datum and every downstairs datum,
at arbitrary universe and in either characteristic. This is a proved
conditional reduction; the unconditional descent theorem remains open.

The chamber correction lemma takes supplied parahoric building data satisfying
the apartment axioms. KP Fact 2.6.22 writes any rational point as a simply
connected image point times a centralizer point. The centralizer point acts on
the apartment through a root-preserving affine automorphism. Affine Weyl
transitivity moves its image of the prescribed chamber back to that chamber.
The existing opposite-pair reflection construction supplies a representative
of this affine Weyl element in the simply connected image. Multiplying this
representative by the inverse of the original simply connected factor gives
the claimed correction.

This is a derived version of the sharp correction used in the corrected proof
of KP Proposition 9.3.24. It uses the published algebraic and affine Weyl
results and retains the apartment axioms explicitly as a premise; it does not
assert existence of building data satisfying those axioms.


The next lemma proves that a chamber-preserving downstairs normalizer point
acts trivially on the apartment if its extension is an upstairs zero point.
Facet preimages put a point and its normalizer translate in the same upstairs
facet. Equivariance identifies their building images with the upstairs zero
action. The explicitly supplied zero-facet property makes their upstairs
apartment images equal. Injectivity of the building embedding and of the
downstairs apartment map then gives pointwise equality on the chamber. A
chamber spans the apartment, so the normalizer affine automorphism is the
identity.

The supplied-data descent lemma combines this argument with the chamber correction to prove
the descent equality for the zero datum of the supplied parahoric building.
The normalizer point lies in the centralizer because its apartment action is
trivial. Character-kernel descent and the actual centralizer translation
formula put its centralizer preimage in the centralizer norm kernel. The
previously proved unramified centralizer comparison then puts it in the
centralizer zero subgroup. Removing the correcting simply connected image
element proves the upper inclusion; scalar extension of zero points gives
the lower inclusion.

The geometric premises remain explicit: apartment axioms for the supplied
downstairs data, `UnramifiedApartmentDescentStatement`, and the upstairs
zero-facet property. Thus this is a conditional reduction, not an
unconditional proof of KP Proposition 9.3.24. It uses only the facet-preimage
clause of apartment descent and does not require a uniquely containing
upstairs chamber.

The global assembly then takes
`ValuationApartmentAxiomsExistenceStatement` to choose valuation data and a
torus, constructs the required zero data using actual derived-cover existence
and connected reductivity of the split-torus centralizer, and applies the
preceding result. Independence of the downstairs zero subgroup identifies the
answer with every supplied downstairs datum, including data based on a
different maximal split torus. The assembly still requires apartment
existence, apartment descent, and the upstairs zero-facet property as explicit
premises.

The final proposition packages these three global inputs using their existing
Library declarations:
`ValuationApartmentAxiomsExistenceStatement`,
`UnramifiedApartmentDescentStatement`, and
`MaximalUnramified.ZeroFacetNoInversionsStatement`.
The theorem `unramifiedZeroDescentGeometricReduction` specializes the third
input to the chosen base-changed group and datum, and applies the global
assembly. Connected reductivity supplies the affine-morphism instance used
by the construction; the conclusion assumes no additional affine instance.

This is derived infrastructure for the proof of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition 9.3.24
(printed p. 343 / PDF p. 374), with the replacement of the first
five proof lines in the authors' corrections of 1 November 2024 (PDF p. 40).
It is not a separately numbered assertion in the source. The implemented
proof uses the published simply connected/centralizer factorization,
affine Weyl representatives, character-kernel descent, centralizer
comparison, and datum independence. It uses no integral models and takes
no zero-descent theorem as an input. It leaves the three geometric inputs
unproved and makes no assertion about the two Galois-stability clauses.
