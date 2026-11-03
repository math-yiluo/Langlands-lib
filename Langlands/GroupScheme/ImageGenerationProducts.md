# Actual finite powers and ordered multiplication

This internal construction supplies the finite-product morphisms in the
generated-subgroup argument of Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), paragraph preceding Proposition 3.3.5, printed p.109
(PDF p.135), registered as `conrad-gabber-prasad-2015-pseudo-reductive`.
The construction itself uses categorical products and the published group
object structure, without a geometric existence or dominance assertion.

For any scheme `V` over an arbitrary base, `finitePower V n` is the actual
categorical product indexed by `Fin n`. `finitePowerPointsEquiv` identifies its
points on every test scheme with ordered families of source points. Its inverse
is the product lift; the inverse, projection, and naturality laws follow from
the universal property. No group structure on `V` is required.

For an actual morphism `f : V ⟶ G.X`, `orderedPowerMap f n` is the ordered list
product of the projections followed by `f`, using the group on morphisms into
the group scheme. `orderedPowerMap_points` proves the ordered evaluation
formula on every test scheme. Precomposition is a monoid homomorphism, so it
preserves the list product. `orderedPowerMap_comp` proves compatibility with
actual group-scheme homomorphisms by the corresponding postcomposition monoid
homomorphism. The empty ordered product is the identity point.

For a conditional actual representative `D : GeneratedImage f`, `D.powerMap n`
multiplies the coordinates of its actual factor morphism. The inclusion
equation and its all-test version identify this with `orderedPowerMap f n`.
The evaluation formula holds in `D.group`. These are intrinsic construction
laws; dominance for some positive power remains a separate geometric target.
