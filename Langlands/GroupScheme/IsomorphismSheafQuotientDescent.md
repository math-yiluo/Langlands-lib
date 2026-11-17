# Scheme representations of the Isom action quotient from local models

Worker 812. This internal construction uses the action quotient of the full
Isom sheaf, the published common-kernel representation theorem, and the
published effective fppf descent theorem for separated locally quasi-finite
schemes. It does not assume a global Isom scheme or cite a new literature
theorem.

`ActionQuotient.withParameter` retains an arbitrary represented relative
parameter `U` alongside a quotient section. The corresponding map from the
full Isom presheaf times `U` is locally surjective.

A `LocalPresentation a U` supplies an actual scheme representing the full
Isom presheaf times `U`, with its original parameter projection, and an actual
quotient scheme over `U`. Its class map is flat, locally finitely presented
and surjective. Its kernel on every relative scheme is exactly equality of
the parameter together with the inverse-precomposition orbit equation for
the supplied action `a`. The quotient scheme's map to `U` is separated,
locally quasi-finite and locally of finite type. All these are explicit
local data and hypotheses.

For a faithful action, the local class map and the canonical quotient map have
the same all-test kernel, using `ActionQuotient.classMap_eq_iff`. Their local
surjectivity gives an actual natural isomorphism between the local quotient
scheme and the canonical quotient sheaf times `U`. Cancellation of the
epimorphic class map proves that this isomorphism retains the original
projection to `U`. It therefore gives the required presheaf pullback square
over the terminal relative scheme.

`representationOfLocalPresentations` takes a covering sieve of that terminal
scheme with such local models. The published
`fppfSeparatedLocallyQuasiFiniteDescent` theorem descends these represented
pullbacks to an actual scheme representing the canonical quotient sheaf.
There is no finiteness or quasi-compactness hypothesis on the whole quotient.
The resulting `Representation.mapToParameter` is the natural class map from
every full Isom family to this actual quotient scheme.

This constructor still requires actual local quotient models with all the
stated laws. It does not produce them from reductivity, identify a general
action as the adjoint action, or represent the full Isom sheaf by a scheme.
Those are additional steps toward the host target.
