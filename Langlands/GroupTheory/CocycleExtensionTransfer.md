# Actual transfer for a normalized cocycle extension

This internal computation concerns the actual group extension attached to a
normalized multiplicative two-cocycle `c`, with a finite acting group and a
commutative coefficient group. It identifies the range of the coefficient
inclusion with the coefficient group and uses Mathlib's `MonoidHom.transfer`.

The quotient by that coefficient subgroup is identified with the acting
group through the original projection. Representatives given by the inverses
of the distinguished section form a left transversal. Reindexing the
coset-product transfer by this transversal gives the explicit formula

`transfer x = product_g ((g • x.left) * c (g, x.right))`.

The factor computation uses the multiplication law of the actual cocycle
extension. There is no cohomological or arithmetic hypothesis in this formula,
and the acting and coefficient groups may have independent universes.
