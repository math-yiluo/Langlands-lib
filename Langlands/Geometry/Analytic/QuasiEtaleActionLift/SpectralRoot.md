# Uniform perturbation of a simple affinoid root

This internal lemma establishes the simple-root perturbation used in the
nearby-lift argument of Berkovich, *Vanishing cycles for formal schemes*
(1994), §7, Lemma 7.3. The reference coefficient map, root, and inverse
derivative live in a fixed normed algebra. The conclusion gives a finite
coefficient test on the base that works after any bounded specialization
to a presented affinoid algebra.

Translate the new polynomial by the image of the reference root. Subtract
the translated polynomial times the image of the inverse derivative from
`X`. The resulting polynomial has a fixed point precisely where the
translated polynomial vanishes. The constant and linear coefficients of
this fixed-point polynomial vanish at the reference data. Each coefficient
is an expression in the derivative inverse and the evaluation of a Hasse
derivative of the original polynomial. Finite spectral tests make the new
constant coefficient small, the linear coefficient at most `1 / 2`, and
the higher coefficients bounded by norms of the reference expressions
plus a common tolerance. The chosen radius makes the higher terms
contracting. The spectral fixed-point lemma then gives a solution whose
spectral displacement lies in that radius.
