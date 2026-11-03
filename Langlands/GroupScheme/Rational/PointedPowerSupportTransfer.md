# Augmentation support transferred by actual ordered product maps

This internal adapter concerns a pointed affine scheme with an actual torus
action, an affine group with an automorphic action, and an actual pointed
equivariant morphism from the scheme into the group. Its ordered product map is
the existing `GroupScheme.orderedPowerMap`; the source carries the existing
pointed finite-power action.

The tuple of distinguished source points maps to the group identity, since
each factor does. Together with the all-test equivariance of ordered products,
this makes the ordered product map pointed equivariant.
`orderedPowerAugmentationPullback` is the actual coordinate pullback restricted
to the augmentation spaces. Its underlying coordinate is precisely the
ordinary pullback. It preserves every all-coefficient-algebra character
eigencondition, and it is injective whenever the full coordinate pullback is.

For an actual split torus, if the source augmentation support lies in an
arbitrary additive subsemigroup and the ordered product pullback is injective,
the target group augmentation support lies in that same subsemigroup. The proof
first transports a nonzero target augmentation eigenfunction to the actual
finite power, then uses the finite-power support theorem. A dominant ordered
product map into a reduced affine group has the required injective pullback by
the existing `dominantPullbackStatement`. The field and universe are arbitrary;
the semigroup need not contain zero, and zero is not inserted.

This is a derived application of the finite-power support calculation and
equivariant pullback, motivated by the product argument in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Lemma 3.3.4, printed pp. 108–109 (PDF pp. 134–135). The dominant-pullback step is
the published reduced-target scheme-theoretic dominance argument. No existence
of a dominant ordered product, generated-image representative, or smooth
generated envelope is asserted here. The exact host
`SemigroupCommutatorStatement` remains a separate proof obligation.
