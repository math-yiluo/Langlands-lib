# Coefficient conjugation of changed sections

This derived helper compares the published coefficient conjugation on actual
rational points with the section base-change homomorphism followed by canonical
ambient descent. It assumes only fields `k`, `K`, a `k`-algebra structure on `K`,
an arbitrary group scheme `G` over `k`, a group scheme `H` over `K`, a homomorphism
`H → G_K`, and a `k`-algebra automorphism of `K`.

`rationalConjugate_map_eq_baseChange_descent` identifies the conjugate of the
image of a point with the image of its changed section under the changed
homomorphism and the canonical descent isomorphism. The proof uses projection
to the original scheme `G`: `rationalConjugate_eq_of_fst` obtains equality from
the coefficient-point equivalence, and
`baseChangeSectionHom_comp_descent_fst` computes that projection by naturality
of section base change and the published descent projection formula.
`baseChangeSectionHom_comp_map` expresses the same naturality after an arbitrary
changed morphism. `baseChangeSectionHom_eq_baseChangeBasePoint` also identifies
the published section homomorphism with the pullback point constructor using
the two pullback projections.

All constructions and comparison results used here are already in the Library,
in `IntegralModel`, `CocharacterTransport`, and `Rational.NormalizerGaloisAction`.
This file is internal infrastructure derived from those definitions and lemmas;
it does not assert stability of an unramified zero subgroup.

`ConjugateSectionNaturalityStatement` packages the generic comparison at any
universe `u`; `rationalConjugate_map_eq_baseChange_descent` proves its pointwise comparison
without additional premises.
