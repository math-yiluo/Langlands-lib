# Unipotent translation covariance of real Whittaker distributions

`Langlands.Global.RankinSelbergGlobal.RealWhittakerTranslationDistribution.RealWhittakerTranslationDistributionStatement`
proves that on the open set of invertible real matrices, invariance under
left upper unipotent translation and covariance under the standard right
Whittaker character determine a distribution by its restriction to the
reversal Bruhat cell. The additive parameter is a nonzero real unit.

The proof differentiates translation by each upper matrix entry group.
Its matrix action has a polynomial time parameter, with inverse at the
negative parameter. The image of the compact support of a test under a
closed time interval is compact and lies in the invertible locus. The
fixed-support differentiation lemma therefore identifies the time-zero
response with the distribution evaluated on the corresponding vector
field derivative. The left response is constant. On the right the
sum of adjacent entries gives the infinitesimal factor of the scaled
additive character. Its common scalar is nonzero. This gives precisely
the infinitesimal laws of `RealBruhatDistributionRestriction`, whose
support descent gives the result.

This internal result uses the right test pullback `X ↦ X * u` in the
character covariance law.
