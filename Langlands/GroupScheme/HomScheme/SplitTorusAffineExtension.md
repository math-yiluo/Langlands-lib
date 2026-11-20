# Descent of maps from a split torus to an affine scheme

The coefficient projection is the map of affine schemes induced by extending
coefficients from \(R\) to \(K\) in the group algebra of an abelian group. The
torsion projection is the map induced by reducing the exponents of a finite
free character lattice \(\Lambda\) in \(\Lambda/n\Lambda\).

Let \(R\to K\) be an injective homomorphism of commutative rings, and let \(Y\)
be an affine scheme. A morphism \(\operatorname{Spec}K[\Lambda]\to Y\)
descends uniquely to \(\operatorname{Spec}R[\Lambda]\to Y\) if its
precomposition with the torsion projection descends along the coefficient
projection for an unbounded set of orders \(n\).

The Lean proof composes each map to \(Y\) with its canonical isomorphism to
the spectrum of its global sections. Full faithfulness of `Spec` translates
the commutative squares into equalities of ring homomorphisms. The coefficient
descent theorem in `TorsionCoefficientDescent` then gives a unique ring map
into \(R[\Lambda]\). Applying `Spec` and the inverse isomorphism of \(Y\)
gives the requested map and transfers uniqueness. This is a derived
scheme-theoretic form of the coefficient calculation in that module.
