# Entire continuation of retained-kernel gamma identities

This internal prerequisite combines the published coefficientwise identity
theorem, finite Laurent actions, and retained-kernel gamma bridge. It makes no
new attribution to the literature.

Let the original and dual bilateral coefficient families be entire in a complex
deformation parameter. Let finite Laurent kernel families `A`, `B`, and `K` have
entire coefficients and parameter-independent finite supports. Reflection
preserves coefficientwise entireness. Applying `K`, then `B` or `A`, and finally
the fixed central scalar also preserves it. The identity theorem applied to each
integer coefficient therefore extends

`(B(u) * K(u)) • reflect(ad(u)) = (C(zeta^e) * A(u) * K(u)) • a(u)`

from all real parameters above a bound to every complex parameter.

The main theorem assumes actual rational continuations and absolutely convergent
spectral expansions of the original and dual families, the finite presentation
`map(A(u)) = map(B(u)) * G(u)`, finite clearing by `K` on the real ray, and actual
gamma functional equations there. Finite clearing on that ray extends to all
parameters by the existing Laurent-clearing theorem; this does not require a
uniform degree bound on its finite output. The retained-kernel bridge converts
each real-ray gamma equation into the displayed coefficient identity. Entire
continuation then supplies the identity at a chosen parameter. The bridge's
converse recovers the complete denominator-guarded gamma equation there, provided
`B` and `K` are nonzero at that parameter.

Original and dual spectral expansions may converge on different right
half-planes, and their bounds may vary with the deformation parameter.
Cancellation occurs only in the rational-function field inside the bridge,
never on arbitrary bilateral coefficient series. This theorem supplies no
representation-theoretic factor certificates, no actual deformation family,
and no unramified gamma transport. Those remain inputs to an application to the
closed adjacent-rank gamma target.
