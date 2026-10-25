# Algebraic reduction for trilinear uniqueness

This internal linear-algebra adapter proves restriction and descent lemmas
for actual complex trilinear forms. It is intended for the published
`EqualRankTrilinearUniquenessStatement`, whose representation-theoretic
hypotheses must still supply the conditional inputs below. It does not prove
that final target or propose additional hypotheses for it. The provenance is
internal: all results follow from linearity, surjectivity, and finite set union.
No external representation-theoretic theorem is asserted here.

`restrict` is the actual linear restriction of a trilinear form to a submodule
in its third variable. `evaluate` evaluates that variable to obtain a bilinear
form. `factor_evaluation` shows that a form vanishing on the kernel of a linear
functional factors through it, by subtracting the scalar multiple of a test
vector where that functional is one.

`eq_zero_of_restrict_eq_zero` assumes invariant linear maps on the test space,
a preserved scalar functional, and vanishing of the corresponding invariant
bilinear forms. If the scalar functional vanishes everywhere, restriction
already determines the form. Otherwise it normalizes a vector where the
functional is nonzero, factors through evaluation, and applies bilinear
vanishing. Thus it does not assume existence of a special Schwartz cutoff.

`uniqueness_of_restriction` applies the kernel result to a nonzero form, uses
proportionality after restriction, and applies the same kernel result to the
difference. The difference has the same invariance by linearity.

The intended instantiation uses evaluation at zero on actual row Schwartz
functions. Mirabolic uniqueness, Frobenius reciprocity, and central spectral
vanishing remain separate obligations. The group action on the test space is
allowed to be any family of linear maps; only its preservation of the scalar
functional is used. In particular, no group-action laws or nonzero scalar
functional are hidden assumptions.

`pullback` composes the first two variables with actual linear maps.
`pullback_injective` uses their surjectivity in each variable. Equivariance of
intertwining maps transports the twisted invariance relation, and
`uniqueness_of_surjective` descends a uniqueness bound on source carriers to
quotient carriers. This is intended for the published `Whittaker.modelMap` and
`Whittaker.modelMap_surjective`; it handles zero functionals without a case
split. The two source carriers and the two target carriers have independent
universes.

`uniqueness_outside_finite_union` takes the union of the exception sets for
restriction uniqueness and residual bilinear vanishing. It chooses that union
before the spectral parameter and every trilinear form. This preserves the
quantifier order required by the parent target.
