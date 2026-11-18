# Proof of representability of finite locally constant étale sheaves

`Langlands.AlgebraicGeometry.finiteLocallyConstantRepresentable` proves
[`FiniteLocallyConstantRepresentableStatement`](FiniteLocallyConstantRepresentableStatement.md)
in every scheme universe `u`. The representability argument follows J. S. Milne,
*Étale Cohomology* (1980), Chapter V, Proposition 1.1, printed pp. 155–156
(registered source `milne-1980-etale-cohomology`, PDF pp. 169–170). Here the
argument applies to sheaves of sets on the full big étale slice site.

## The split model

Over a trivializing scheme `U` with finite discrete value set `A`, take the
coproduct of copies of `U` indexed by `A`. A map from a scheme `T` over `U` to
this coproduct gives a continuous label on `T`. Conversely, the fibres of a
continuous label are pairwise disjoint opens covering `T`. On the fibre
labelled `a`, the map is the structure map to `U` followed by the inclusion
of summand `a`. The disjoint-open gluing theorem gives a unique map from
these restrictions, and the label assignment commutes with precomposition.
The projection is étale and locally quasi-finite by locality on the source.
It is proper by the finite coproduct theorem for proper morphisms, hence
finite by properness and local quasi-finiteness.

## Descent and gluing

Over an affine base, `QuasiCompactCover.exists_hom` refines the trivializing
cover by finitely many affine schemes. Pull back the local models along the
refinement. The restriction of the sheaf to the coproduct of the refined
covering schemes has these models on its open summands.
`LocalRepresentation.exists_representation_zariski` glues them, and target
locality gives a finite étale model over the coproduct. The coproduct is
affine and its map to the base is étale and surjective.

`Picard.LocalRepresenter.etaleRelation` extracts the cartesian descent
relation from the glued representation. The model is affine because it is
finite over an affine base, so its whole space supplies the invariant
quasi-affine open required by
`EtaleRelationQuasiAffineEffectivity.exists_effective_of_invariantQuasiAffine`.
The resulting square identifies the local model with the pullback of the
descended scheme. `Picard.LocalRepresenter.representableByDescent` identifies
the descended scheme's functor of points with the given sheaf. Finiteness
and étaleness descend along the coproduct map, which is surjective, flat and
quasi-compact.

For an arbitrary base, apply the affine argument to the pullback of the
trivializing cover over each member of the affine open cover. Zariski
gluing gives the global representation and target locality gives a finite
étale structure map. The proof lifts the sheaf's values from `Type u` to
`Type (u + 1)` to use the Library's gluing interface, then transports the
representation back to `Type u`.
