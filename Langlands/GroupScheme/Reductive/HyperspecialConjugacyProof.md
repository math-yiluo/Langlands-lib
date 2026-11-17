# Proof of the hyperspecial conjugacy criterion

Worker 843 and Worker 263.

`Langlands.GroupScheme.reductiveHyperspecialConjugacy.{u}` proves exactly the
published proposition
[`ReductiveHyperspecialConjugacyStatement`](HyperspecialConjugacyStatement.md).
It retains every universe, local-field, split reductive group, and supplied
adjoint quotient quantifier of that statement and has no additional
hypotheses. The statement and its import closure are unchanged.

The statement corresponds to Brian Conrad, *Reductive group schemes* (2014),
Proposition 7.2.14, p.260; its source translation is documented in the
statement's Markdown. The implemented proof uses the published dense bounded
normalizer theorem and maximal compactness of integral points. It does not
use Conrad's Cartan decomposition and root-coordinate argument. In fact,
this route does not need the target's splitting premise, which is retained
in its unchanged type.

Let \(R=\mathcal O_F\), and write \(G_F,A_F\) for the actual generic fibres of
the supplied integral groups \(G,G^{\mathrm{ad}}\). The proof forms
`IsRelativeAdjointQuotient p` from the given reductivity, flatness,
surjectivity, local finite presentation, and full-centre kernel hypotheses.
The published `fieldQuotient` theorem makes the generic target \(A_F\)
adjoint. The canonical models
[`IntegralModel.ofReductive`](../IntegralModel/OfReductive.md) retain the
original integral groups and identify their generic fibres by the identity.

The proof first establishes integral-normalizer detection. Put
\(H=p(G(R))\subset A_F(F)\). The actual pullback point equivalences identify
the canonical models' integral-point images with the original restriction
images. Naturality of those equivalences for \(p\) identifies \(H\) with the
image of the restricted \(G\)-points under the point homomorphism of \(p\).
`Subgroup.map_equiv_normalizer_eq` transports normalizers through this same
specified equivalence.

The quotient action intertwines \(p\) with conjugation on the quotient, by
[`AutomorphicAction.act_comp_eq_conjugation`](../AutomorphicAction/QuotientNormalizer.md).
Consequently every adjoint point preserving the restriction image of
\(G(R)\) normalizes \(H\). In particular, every \(A(R)\)-point does so,
because naturality makes a restricted acting point preserve that image.
These statements supply the explicit normalization premise of
[`IntegralModel.normalizer_map_integralPoints_eq`](../IntegralModel/AdjointNormalizer.md).

That theorem applies because the generic source is connected reductive,
the generic target is adjoint, the generic quotient is dominant, and the
target canonical model has connected reductive special fibre. Its proof
uses openness of \(G(R)\) to obtain Zariski density, compactness to obtain
boundedness of \(H\), and the dense bounded normalizer theorem in the adjoint
group to make the closure of \(N(H)\) compact. Since this closure contains
\(A(R)\), published maximal compactness forces \(N(H)=A(R)\). Thus every
point preserving \(G(R)\) is itself restricted from \(A(R)\).

Finally, the generic
[`conjugacy_iff_factorization_of_preservesRestrictionImage`](../AutomorphicAction/RestrictionImage.md)
reduction converts this normalizer detection into the required equivalence.
The quotient-action lifting law supplies its conjugation premise. For the
forward direction, removing the conjugating lift leaves an integral adjoint
point; for the reverse direction, a restricted adjoint point preserves the
integral image and the lifted factor acts by conjugation.

The private proposition `IntegralNormalizerCriterion` organizes the
intermediate detection assertion. It is proved in this module and supplied
to the final reduction; it is not a hypothesis of the exported theorem.
