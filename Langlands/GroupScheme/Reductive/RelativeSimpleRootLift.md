# Fppf simple-root values in supplied torus coordinates

This internal derived module specializes independent-monomial local lifting to
the simple roots of a supplied `AffinePinnedModel`. It retains an actual
coordinate isomorphism to a supplied torus, expresses the lifted point in that
torus, and calculates its values under the actual fixed-exponent simple-root
characters on every refinement. The construction is over the model's arbitrary
commutative coefficient ring.

For a model `M`, a group scheme `T` over `M.base`, and an isomorphism
`e : splitTorus M.base M.coordinates ≅ T`, the homomorphism
`M.simpleRootCharacter T e a` is
`splitTorus.exponentCharacterOnTorus M.base T e (M.rootDatum.root a)`.
Thus it is the actual character obtained by transporting the model's
simple-root exponent vector through the specified coordinates. No independent
identification with characters of an ambient reductive group is asserted;
that identification depends on the coordinate data used by a consumer.

Given a test scheme `V` over `M.base` and global units indexed by
`M.basis.support`, `M.simpleRootUnitsLift V c` specializes the canonical
independent-monomial lift. Its independence hypothesis is discharged by
`M.basis.linearIndepOn_root.linearIndependent`, the independence of the roots
in a root-datum base. The result retains the covering test scheme, projection,
coordinate-torus point, commutative square, and flatness, surjectivity and local
finite presentation of the projection.

`M.simpleRootUnitsLift_character` states that the lifted point, transported
through `e.hom`, has each prescribed simple-root unit value after pullback to
the cover. `M.simpleRootUnitsLift_character_naturality` retains that equation
on every refinement. Finally, `M.exists_fppf_simpleRoot_values` gives the
existential form: there is a flat, surjective, locally finitely presented
`b : W ⟶ V` and an actual point `t : W ⟶ T.X` whose simple-root character
values on every refinement `d : U ⟶ W` are the units pulled back along
`d ≫ b`.

All three proofs specialize the corresponding arbitrary-weight actual-character
theorems in `RelativeExponentCharacterLift`. This explains their internal
derived provenance. The module assumes the model and the coordinate isomorphism;
it supplies neither a pinning-existence theorem nor the final isogeny
torus-rigidity proof. It imposes no field, nonzero-ring, reducedness or
noetherian hypothesis, and no saturation hypothesis on the root sublattice.
