# Actual normalized second adjointness

This file states `Langlands.Parabolic.NormalizedSecondAdjointnessStatement`,
the conjunction of `StandardSecondAdjointnessClause` and
`RefinedSecondAdjointnessClause`. All three declarations are Prop-valued
definitions. This contribution supplies a specification, not a proof.

## Scope and actual representations

Each clause quantifies a prime, a `PadicField` of universe `uF`, its supplied
compatible `TopologicalData`, a positive natural rank, and a `BlockShape B`.
The refined clause also quantifies `BlockRefinement S`. The inducing carrier
has universe `uV` and the ambient representation carrier has universe `uW`;
these three universes are independent. The induced carrier can have universe
`max uF uV`.

In the standard clause the inducing representation `σ` is on `B.Levi F.Carrier`
and `π` is on the actual general linear group. In the refined clause `σ` is
on `refinedLevi F.Carrier B S` and `π` is on the product Levi `B.Levi F.Carrier`.
Both representations are admissible; the Library's `IsAdmissible` includes
smoothness. The refined input is an arbitrary representation of the product
group. No tensor decomposition, irreducibility, cuspidality, finite length,
or finite dimension of the whole carrier is assumed.

For each group and parabolic, the conclusion is one family `E` of complex-linear
equivalences, for all such admissible `σ` and `π`:

\[
 E_{\sigma,\pi}:\operatorname{Hom}(i_P\sigma,\pi)
       \simeq_{\mathbf C}\operatorname{Hom}(\sigma,r_{\bar P}\pi).
\]

The left Hom consists of actual `Representation.IntertwiningMap`s from
`T.normalizedParabolicInduced B σ.ρ`, or `T.normalizedRefinedInduced B S σ.ρ`.
These are the Library's smooth induced function spaces with right translation
and positive upper half-modulus covariance. The standard right Hom uses
`CuspidalJacquetMultiplicity.oppositeJacquet T B π`, the actual lower-radical
coinvariants with the normalized action transported through `B.leviEquiv`.
The refined right Hom uses `T.normalizedRefinedOppositeJacquet B S π.ρ`, on
the actual refined lower-radical coinvariants and common refined Levi.

For both opposite quotients the full opposite modulus is the inverse of the
upper full modulus. Thus inverse-half Jacquet normalization gives the positive
upper half-modulus. The absolute value in these constructions is the Library's
`q^(-valuation)` absolute value. There is no change to the existing constructions
or normalization characters.

## Naturality and downstream use

The family is contravariantly natural in the inducing representation and
covariantly natural in the ambient representation. For actual intertwiners
`a : σ' → σ`, `b : π → π'` and `f : i_P σ → π`, the two equations are

\[
 E_{\sigma',\pi}(f\circ i_P(a))=E_{\sigma,\pi}(f)\circ a,
 \qquad
 E_{\sigma,\pi'}(b\circ f)=r_{\bar P}(b)\circ E_{\sigma,\pi}(f).
\]

Lean states these equations pointwise on each vector of the appropriate
inducing representation. The induced maps are the existing normalized induced
maps. In the standard target equation `Jacquet.map` is the actual map on
coinvariants; normalization and pullback change its action types but leave its
underlying linear function unchanged. Both sides therefore have the exact
normalized quotient carrier. The refined target equation directly uses
`normalizedRefinedOppositeJacquetMap`. All compared representations are
admissible, and naturality is within the fixed carrier universes of each family.

Every linear equivalence preserves and reflects zero, hence relates nonzero
maps in these two Hom spaces. Once admissibility and nonvanishing of induction
are separately available, instantiate the ambient carrier universe at
`max uF uV` and apply the family to the identity of `i_P σ`. Its image is a
nonzero map `σ → r_opP(i_P σ)`; for irreducible `σ` this map is injective.
For irreducible `π`, a nonzero map `i_P σ → π` is surjective. These are intended
downstream consequences of the statement and those additional hypotheses;
this file neither proves them nor assumes them as inputs.

## Provenance

This is an internal admissible specialization of second adjointness, formulated
for the Library's actual GL and refined product-Levi functors. Its original
source is Bill Casselman, *Introduction to admissible representations of
p-adic groups*, Chapter III, revision April 29, 2019, registered as
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The source's opening paragraph covers connected reductive groups, hence both
GL and a finite product of general linear groups. Page 1 specifies positive
half-modulus covariance and right translation. Proposition III.1.1, page 2,
identifies the contragredient of normalized induction with induction of the
contragredient. Proposition III.3.5, page 4, gives normalized first adjointness.
Theorem III.6.2 and Corollary III.6.3, pages 7–8, identify the opposite Jacquet
module of the contragredient with the contragredient of the Jacquet module via
the canonical pairing. The opposite overbars in these formulas were checked
in the original page images. The field-coefficient restriction introduced on
page 7 is satisfied by complex coefficients.

The resulting admissible duality route is to dualize a map out of `i_P σ`,
use induction-duality and first adjointness, and then use opposite Jacquet
duality and admissible reflexivity to obtain a map from `σ` to `r_opP π`.
The stated naturality is the compatibility of this composition with actual
intertwiners. This combined GL/product-Levi family is an internally derived
formulation, not a claim that Casselman prints this exact combined statement.
His page 8 remark also identifies Bernstein's broader second-adjointness
extension. No unpublished Bernstein assertion is used as a formal premise.

Silberger, *The Langlands quotient theorem for p-adic groups* (1978),
Section 2, page 97, and the proof of Lemma 5.3, page 100, motivate the
quotient direction needed by the consumer. The registered retained source is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
These passages were read in the original; they are motivation, not a substitute
for proving this Hom equivalence or the unrestricted wording of Lemma 5.3.
No source-specific errata file was present in the public notes when checked.

The file introduces no duality or reciprocity certificate as a hypothesis.
Proving this statement requires establishing and assembling its actual
adjunction or duality maps. It does not prove the relative multiplicity
comparison or its irreducible-head consequence.
