# Product-induced preimages of ambient coefficients at the full root

At the literal full Levi, pullback to the Levi and back to the ambient group
acts by the identity on group points. The resulting equivariant identity
on the representation carrier preserves ordinary coefficients. This is
the coefficient identification used for the prescribed value in the proof
of Waldspurger VIII.4.2, printed p. 330 (PDF p. 96).

`rationalFullLeviAmbientInducingEquiv` proves equivariance by evaluating
the composite group map at each ambient point. Its coefficient tensor
transport composes with the full-root product coefficient equivalence,
which uses the original compact-probability map. Applying the inverse of
the composite linear equivalence to the prescribed ambient tensor gives
the product-induced value at the pulled-back inducing representative.
The two coefficient comparison laws give equality of the resulting
locally constant function with the original coefficient. The
representation carrier remains in `uV`.
