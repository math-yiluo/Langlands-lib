# Pushforward of a weight integrable over compact preimages

Let `p : X → Y` be measurable, where `Y` is a second countable locally
profinite space with its Borel structure. Suppose `μ.map p` is absolutely
continuous with respect to a σ-finite measure `ν` on `Y`. If a complex weight
`f` is integrable against `μ` on `p ⁻¹' K` for every compact `K ⊆ Y`, then
`locallyIntegrablePushforward` gives a locally integrable density `r` on `Y`.
For every Schwartz–Bruhat test `g` on `Y`, it satisfies
\[
\int_Y r(y)\,g(y)\,d\nu(y)=\int_X f(x)\,g(p(x))\,d\mu(x).
\]

The proof defines the distribution on `Y` by the integral on the right.
The pulled-back test is bounded and supported in the preimage of its
compact support. The hypothesis on `f` gives integrability there and
hence on all of `X` for the product in that integral.

At a point of `Y`, choose a compact neighborhood `K` and restrict `μ` to its
preimage. The pushforward of this restricted measure is still absolutely
continuous with respect to `ν`, and `f` is now integrable for the restricted
measure. The theorem `integrablePushforward` gives an integrable density for
this restriction by Radon–Nikodym. It represents the distribution for tests
supported in the interior of `K`. The theorem
`Distribution.exists_locallyIntegrableDensity_of_locally` glues these
representations into the claimed density.

The lemma combines the test integral identity for pushforward with local
integrability over inverse images of compact sets. It provides the density
step in a submersion proof of the local summability clause of Harish-Chandra,
*Admissible invariant distributions on reductive p-adic groups*, ULS 16
(1999), §1.4, Lemma 1.13, p. 10. In that application the map sends `(k, W)`
to `k W k⁻¹`, with `k` in a compact subgroup, and the weight is pulled back
from the Levi Lie algebra.
