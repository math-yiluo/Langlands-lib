# The parameter scheme of a maximal torus whose normalizer is the whole group

Author: Worker 1420.

This internal, derived module treats the degenerate case of the
maximal-torus unirationality target: every point of `G`, over every test
scheme, normalizes the torus. The field `k : Type u` is arbitrary; there is
no infinitude, perfection or characteristic assumption.

`IsUnirational.of_section_denseRange` proves that a scheme `X` over `k` is
unirational when it has a ground-field section `s : Spec k → X`
(`s ≫ X.hom = 𝟙`) with dense underlying range. The parametrization uses the
zero-dimensional affine space `𝔸(PEmpty; Spec k)` and its top open, which is
nonempty because affine space surjects onto `Spec k`. The morphism is the
inclusion of the top open, followed by the structure map to `Spec k`, then `s`.
It is a morphism over `k` because `s` is a section. Its range is the range of `s`, because `Spec k` has
exactly one point. Unirationality then follows from
`IsUnirational.of_open_denseRange` in `UnirationalSpreading`, applied to
`isUnirational_affineSpace`.

`IsMaximalTorusParameter.range_one_eq_univ` assumes an actual parameter
map `q : G.X → Q` for `j₀` and assumes that every point `g : U → G.X`, for
every scheme `U` over `k`, lies in `torusNormalizer j₀`. It proves that the
image of the identity section `1 ≫ q` is all of `Q`. Let `y` be a point of `Q`. Surjectivity of `q`
gives a point `x` of `G` over it. Take `U = Spec κ(x)` and let `g` be its
canonical morphism to `G`. Then `g⁻¹ * 1` lies in the normalizer, so the
all-test fiber relation `fiber_iff` gives `g ≫ q = 1 ≫ q`. The identity
point over `U` is the identity section over `Spec k` precomposed with the
structure map (`MonObj.comp_one`). Evaluating both sides at the unique
point of `Spec κ(x)` shows that `y = q(x)` lies in the range of `1 ≫ q`.

`IsMaximalTorusParameter.isUnirational_of_normalizer_eq_top` combines these two
results. Under the same hypotheses, `Q` is unirational over `k`. The section is
`(1 ≫ q).left`, which is a section because `1 ≫ q` is a morphism over
`Spec k`. Maximality of the torus and the remaining parameter properties
are not used.

Provenance: this is derived from the published `IsMaximalTorusParameter`
predicate (its surjectivity and all-test fiber fields), the published
`IsUnirational` predicate, and the spreading-out helper module. In the
induction of SGA 3, Exposé XIV, Théorème 6.1, this is the case where `G` is nilpotent and the scheme of
Cartan subgroups is a single rational point. The module does not prove the
general maximal-torus unirationality target.
