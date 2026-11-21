# Coherence of the actual translated comparisons

`Langlands.Plancherel.ActualConjugateLeviCoherence.ClosedV32Statement` is a
closed statement of the algebraic compatibility of the normalized
comparisons of Waldspurger, *La formule de Plancherel pour les groupes
p-adiques* (2003), V.3 formula (1) and Lemma V.3.2, printed p. 295,
PDF p. 61. The actual rational representatives belong to the common
compact subgroup. The parabolics use actual common-centralizer
cocharacters, and the field and smooth representation-carrier universes
remain independent.

`LeviNormalization` displays the split-central quotient and its actual
Haar measure, square integrability and irreducibility. The closed target
and each family certificate require `HasSourceNormalization`. The anchor
cocharacter factors through an actual maximal split torus in the Levi, and
`K` is the maximal compact norm-one fixer of a special vertex in the
compatible apartment of that torus. The quotient Haar measure has mass one
on the image of the compact Levi trace. This is the Weil quotient scale
from I.1, printed p. 240, used by the inverse formal degree in III.1 (3),
printed p. 265, and the form of V.2, printed p. 293. `CompatibleHaar` uses
pushforward along the quotient isomorphism of the actual inverse Levi
conjugation. `hasSourceNormalization_conjugate` proves that the conjugate
Levi data have the corresponding source normalization. For a translated comparison, `IsActualComparison`
quantifies over the exact common-Levi normalized comparison for the
conjugate source and target parabolics. That certificate witnesses
actual forward and reverse dual continuations, their scalar inverse
and dense generic locus, a regular extension on all unitary points,
and uniqueness by the rational germ. The translated family must be
its composition with the already constructed `unitaryTranslation`.
The certificate uses indexed equality for the two presentations of this
family type.
Its two fibers carry the actual coefficient maps and inverse-formal-degree
forms, with the source compact probability. The certificate requires
these identities and bijectivity on every unitary parameter.

The existence assertion applies to the displayed structural inducing
data at these source scales, with compatible quotient Haar measures. The independence assertion
compares any two witnesses for the same displayed data, including
independently chosen continued presentations. The composition law applies
the certified comparison for `t`, followed by that for `s` at the
transported unitary point. `multiplicationEquiv` identifies the twice
conjugated target with the direct target for `s * t`. Their images must
agree for every coefficient vector. The identity and inverse assertions
use the corresponding canonical target-fiber identifications, with both
inverse identities required. The pointwise equality predicates place
indexed equality at the interfaces between the actual fiber expressions.
`transportedValue_iff`, `transportedComposite_iff`, and
`transportedInverse_iff` prove that these predicates give the ordinary map
equations when the types are written identically. The assertions of
existence, independence and coherence are Prop-valued targets.
