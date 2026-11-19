# From chamber bounds to global orbit section estimates

This derived reduction implements the finite translation step of Waldspurger's
proof of Proposition VI.3.1, printed pp. 302–303, in the existing fixed-level
section topology. [Waldspurger (2003)](https://doi.org/10.1017/S1474748003000082)

`OrbitSectionChamberDerivativeEstimates` is a pointwise estimate on a
specified set `S` of ambient group points. At each input level and real
order `r`, its finite input derivative supremum and nonnegative scalar
bound the operator's values on `S` with the kernel `Ξ(m) * (1 + σ(m))^(-r)`.

`orbitSectionSchwartzEstimates_of_compact_chamber` uses a double cover
`G = A S B` with `A` and `B` compact, same-level bi-invariance,
and covariance under the actual translated section.
Both weights are bi-invariant under a common open subgroup. The spherical
weight has a uniform translation bound, and height is nonnegative,
subadditive and invariant under inversion. Under these hypotheses the same
kind of derivative control holds for the whole-group Schwartz seminorms.

The proof covers `A` and `B` by finitely many left and right cosets of
the input open subgroup `H`. Bi-invariance absorbs their `H` factors.
Each remaining translation is evaluated by applying the translated section
to a point of `S`. The translated level lies inside `K`, so the given
chamber bound applies. `exists_orbitSectionLevelTranslate_finsetSup_bound`
returns a finite derivative supremum on the original level. The finite
union of these indices controls all translates. The weighted translation
bound and its uniform form for the compact group `H` compare the kernels
at the chamber point and at the original group point. Multiplying by the
reciprocal kernel and taking the supremum yields the requested
extended-nonnegative Schwartz seminorm bound.

`inducedOrbitWavePacket_translateLevel` derives the covariance for the
original orbit integral with any displayed weight and character measure.
It applies integral congruence to the published coefficient identity.
The two packet arguments are a translated section at `g` and the original
section at `x₂⁻¹ g x₁`. Both integrals use the same orbit measure.
