# Open charts of closed multiplicative-type subgroups

Author: Worker 872.

`MultiplicativeTypeSubgroupModuli.IsOpenChart j` says that an actual
closed subgroup family of relative multiplicative type over a smooth
parameter scheme has an evaluation map which is injective on every
test scheme. Its pullback along every actual closed multiplicative-type
family is represented by an open subscheme of that family's base:
the existence of a parameter over a further test scheme is equivalent
to its structure morphism having image in that open subscheme.

`CoversFieldPoints j` says that each actual closed multiplicative-type
subgroup over each field-valued point of the base is an evaluation of
one of the specified families. It asks for an actual point over the
same field; no field extension is allowed in this conclusion.

The multiplicative-type property is the imported fppf-local finite
character-group property and permits torsion characters, nonsmooth
finite factors and nonsplit forms. Evaluation reuses the generic
`TorusSubgroupModuli.familyHom` and `evaluate` constructions, which
have no torus hypothesis.

These are internal chart interfaces for a proof of the smooth moduli
consequence of SGA 3, Exposé XI, Theorem 4.1 (registered source
`sga3-exposes-xi-xii-xiv-gille-polo-2008`, `Expo11.pdf`, PDF p.20,
recomposed p.104, original p.157). They generalize the published
`TorusSubgroupCharts` interfaces by changing the source property to
relative multiplicative type. This module constructs no chart and
asserts no chart-cover existence theorem.
