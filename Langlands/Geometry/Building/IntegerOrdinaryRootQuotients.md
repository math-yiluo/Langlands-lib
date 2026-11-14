# Missing ordinary directions and doubled-root cosets

`HasNoOrdinaryRootDirection` abbreviates the assertion that no ordinary affine
root has the specified actual relative-root form as its derivative.

This internal adapter extends the finite improvement argument already implemented
in `ValuationDerivativeAffineRoots` from local fields to integer-valued building
data over an arbitrary field. It uses full V6 and opposite factor pairs for
bounded finiteness of root values. It requires no topology or completeness.

V4 embeds the doubled-root filtration at depth `2r` in the root filtration at
`r`. If the ordinary derivative direction `a` is missing, the definition of an
ordinary affine root factors each nonidentity root element as an element with
strictly larger value times a doubled-root element at twice the original value.
If a coset could not meet a prescribed higher filtration, its possible values
would lie in a bounded interval. Bounded finiteness supplies a maximum, and the
strict improvement contradicts maximality.

The original argument is KP Lemma 6.3.9, using Proposition 6.3.7; the later
closure step of that lemma is not used here. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`. This module alone proves no
ordinary derivative equality.
