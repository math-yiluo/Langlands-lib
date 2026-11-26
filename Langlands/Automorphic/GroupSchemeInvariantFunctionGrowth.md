# Uniform derivative growth of automorphic inducing functions

`exists_uniformGrowth_functionInfiniteSlices` works with the family of all infinite slices of
a smooth scalar function. Compact finiteness for a maximal compact of the infinite group,
a common cofinite ideal of the enveloping center, and moderate growth give one nonnegative
exponent for all enveloping derivatives on all slices. This applies to functions on the
inducing quotient `U(𝔸) M(F) \ G(𝔸)`.

The proof uses componentwise right translation and the componentwise enveloping action
`sliceFamilyEnvelopingAction`. Faithful evaluation identifies the compact orbit with its
scalar-function realization. For directions tangent to compact curves, difference quotients
in that finite-dimensional span show that the derivatives preserve the span. The cofinite
center ideal makes the center orbit of the input family finite dimensional.

The adapted Casimir expresses the full tangent square sum as a central operator plus a compact
square sum. The latter preserves the compact orbit span and commutes with the center. Applying
the finite-dimensional stability argument to the span of its powers on the input family gives a
finite-dimensional space stable under both actions. A monic polynomial in the full square sum
annihilates the family. Its leading symbol is a power of a sum of squares in spanning real
directions, so all left translates of every slice satisfy one elliptic equation. The published
`lieGroupEllipticInteriorEstimate` bounds each derivative by the undifferentiated function on
right translates of a compact set. The compact-translate moderate-growth bound absorbs these
translates at one exponent. The comparison `plotSmoothEnvelopingAction_wordHom` identifies the
word operators with the Library's actual archimedean enveloping action.

The result implements the uniform derivative-growth conclusion for automorphic functions in
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.2.3, p. 25, and
I.2.17, pp. 37–39, using the adapted Casimir and elliptic estimate from the Library's proof for
rational-invariant forms. The registered source `moeglin-waldspurger-1995-spectral-decomposition`
contains `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, SHA-256
`296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`.
