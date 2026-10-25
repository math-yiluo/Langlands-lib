# Anti-automorphism pullback on Hecke convolution

This internal construction equips the existing pullback of actual test functions
with its multiplicative law into the opposite Hecke algebra. It is a prerequisite
for convolution-kernel arguments; it does not prove Whittaker multiplicity one or
invariance of any distribution.

Let G be a topological group with its Borel measurable structure, mu a measure
invariant under right translations and inversion, and tau a homeomorphism of G
satisfying tau(xy) = tau(y)tau(x). Assume tau preserves mu. Then
`TestFunction.pullback_convolution` proves

`pullback tau (convolution mu f g) = convolution mu (pullback tau g) (pullback tau f)`.

The convolution is exactly the published integral convention
`(f * g)(x) = integral f(y) g(y^{-1}x) dmu(y)`. The proof first deduces that tau
preserves the identity and inverses. It substitutes y = tau(u) using measure
preservation, rewrites the second factor as g(tau(x u^{-1})), and then substitutes
u = v x followed by v = z^{-1}. The resulting integrand is
`f(tau(z^{-1}x)) g(tau(z))`; commutativity of complex multiplication gives the
reversed convolution. These are Mathlib's Bochner integral substitution laws,
which also respect its convention for nonintegrable functions, so this identity
does not itself require finite mass on compact sets.

With the additional assumptions that mu is left invariant and finite on compact
sets, the published `HeckeAlgebra mu` is a nonunital complex algebra.
`HeckeAlgebra.antiPullback` constructs a `NonUnitalAlgHom` from that actual
convolution algebra to its multiplicative opposite. Its underlying map is
`f -> op (f composed with tau)`; additivity, scalar compatibility and zero
preservation come from the published `TestFunction.pullback`, while
multiplicativity is the displayed reversal identity.
`antiPullback_apply` records its pointwise value and `antiPullback_bijective`
uses the pullback linear equivalence and the opposite-type bijection.

No involutivity of tau, Haar normalization, positivity, Hausdorffness, local
compactness or total disconnectedness of G is additionally assumed. These
hypotheses can be supplied by later applications but are unnecessary for this
construction. The provenance is internal: the module derives the map solely
from the published `Hecke.Convolution`, `Hecke.TestFunction` and Mathlib's
measure-preserving, right-translation and inversion substitution theorems. It
makes no claim to transcribe a separate literature result.
