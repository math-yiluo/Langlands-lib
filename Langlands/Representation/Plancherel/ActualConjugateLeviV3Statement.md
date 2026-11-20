# Closed translated V.3.1 target

`Langlands.Plancherel.ActualConjugateLeviV3.ClosedV31Statement` states the full
unitary extension and preservation properties for the actual translated
standard tensor. The source is J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques* (2003), V.3 formula (1) and Lemma V.3.1, printed p. 295,
PDF p. 61, registered as `waldspurger-2003-plancherel`. The whole-operator
rational convention comes from IV.1, printed pp. 276–277. The compact
probability is fixed by I.1 and used in V.1. The inverse formal degree
of III.1 (3) scales the product form of V.2.

The field is any nonarchimedean local field and the ambient group is affine,
locally of finite type, and connected reductive. The representation carrier
universe is independent of the field universe. The parabolics are the actual
dynamic parabolics of the source cocharacter and the target cocharacter. The
target has the centralizer of the conjugated source. The displayed compact
open subgroups give the actual factorizations for the source, conjugate source,
and target. `HasSourceNormalization` specifies that the source cocharacter
factors through an actual maximal split torus and that the source compact
is the maximal compact norm-one fixer of a special vertex in its compatible
valuation apartment. The torus lies in the source Levi. Its actual conjugate
lies in the target Levi and therefore in both target-side parabolics.
The compact on the target side is the conjugate of the source compact.
`isSourceCompactFor_conjugate` transports the special point and compact to
the conjugate apartment. For a Weyl representative in the source compact,
`RationalDynamicSource.conjugateCompact_eq_self` gives the same compact.

`unitaryConjugateParameter` is the published restriction along the inverse
isomorphism of the actual parameter schemes, specialized to norm-one
characters. The generic map uses the full `conjugateParameter` along that
same inverse isomorphism.
`compactComparison` conjugates that particular generic map by the actual
`compactTensorEquiv` on either side. The source uses the original inducing
object and the target uses its literal conjugate. The compact square follows
from cancellation of the source equivalence. The ambient map remains precisely
left translation followed by the actual forward continued standard operator
tensored with the inverse of the actual reverse dual continuation.

The inducing object is irreducible and square integrable modulo its actual
split center. The target central subgroup is transported through Levi
conjugation. The source measure has mass one on the image of the compact Levi trace
in its actual split-central quotient. The normalization module proves that
this is the Weil quotient scale for the two trace-normalized Haar measures.
The displayed quotient homeomorphism pushes the target Haar measure to that
source measure. `isSourceQuotientHaar_conjugate` gives the exact target scale. `conjugate_squareIntegrable` and
`conjugate_irreducible` apply the published transport theorems to those same
actual data. `PreservesCoefficientsAndForms` uses the coefficient maps and
inverse-formal-degree forms already defined in `ActualCommonLeviV3`, with
the stated compact Haar probabilities and the compatible quotient Haar
measures. It requires bijectivity, the coefficient identity, and equality
of the Hermitian inner products at every unitary parameter.

`IsActualNormalizedComparison` specifies the family of actual product-action
intertwiners with the source normalizations and existential forward and reverse dual continuation packages
and scalar inverse data. It requires a nonempty genuine generic locus with
ambient and unitary density, including an open dense sublocus. It requires
whole-operator rationality on that locus. Each unitary point has an ambient
open neighborhood with a polynomial operator numerator and one denominator
nonzero throughout the neighborhood. This single quotient describes the
family throughout the unitary part of the neighborhood. All local regular
representatives of the actual germ must give the specified value. Wherever
the generic locus meets the unitary subgroup, `AgreesOnUnitaryGeneric` equates
the compact realization of the unitary value with `compactComparison`.
Both realizations use the source and target compact tensor equivalences.

`ClosedV31Statement` takes those structural normalizations and requires the existence of a family with all these
properties. These are statements for the whole tensor, so cancellation of
poles of its factors is allowed. The analytic existence, rationality,
regularity, and preservation are open targets. The internal packaging
specializes the published actual coefficient models, quotient transport,
and compact tensor constructions to the rational-conjugation formula.
