# Ordinary Weyl orbit decomposition

`OrdinaryWeylOrbitDecompositionStatement` applies to any field `F`, any rank
`n`, and any set of conjugacy class representatives in `WeylTorus F n`.
This type consists of subgroups that occur as centralizers of regular
semisimple elements of `GLₙ(F)`. A matrix is regular semisimple exactly when
it lies in the image of the ordinary Weyl map for exactly one representative.
For every `T : WeylTorus F n`, each nonempty fiber of its map has positive
finite cardinality equal to the order of its rational Weyl group. In the
local-field setting, [Weyl integration data](WeylIntegrationData.md) identifies
these subgroups with the rational points of the maximal tori used in
Henniart–Lemaire (2011), II.2.10, formula (2).

For `T : WeylTorus F n`, `WeylTorus.ordinaryOrbitMap T`
sends a left coset `T x` and a regular point `γ` of `T` to `x⁻¹ γ x`.
The centralizer of any regular point of `T` is `T`. To prove this, compare it
to the centralizer of the regular element defining `T`. Each of the two
elements commutes with the other, and commutativity of each centralizer gives
the two inclusions. Thus conjugation descends to the coset space. Conjugation
preserves characteristic polynomials and transports centralizers, so a
regular semisimple matrix lies in the image for `T` exactly when its centralizer
is conjugate to `T`. The representative property then gives the unique torus.

The fiber over `x⁻¹ γ x` has a bijection with the rational Weyl group. A
normalizer element `k` gives the pair `(T k⁻¹ x, k⁻¹ γ k)`. In a fixed fiber
the coset determines the torus point, since both torus points can be conjugated
by the same coset representative. The coset projection also identifies exactly
the normalizer elements in the same class modulo `T`.

For surjectivity, if `(T y, t)` is in the fiber, `k = x y⁻¹` conjugates
`γ` to `t` under `k⁻¹ · k`. Both centralizers are `T`, so `k` normalizes `T`.
It gives the coset `T y` in the fiber. `WeylTorusFinite` supplies finiteness
and positivity of the resulting cardinality.
