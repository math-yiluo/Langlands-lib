# Models of actual Levi images from sheaf descent

This internal assembly module combines the local point and generic cocycle
constructions. For a relative parabolic in a reductive group and a supplied
relative radical, the closed radical is affine over the base and smooth.
On an affine base, the supplied Zariski sheaf condition produces a local
Levi section over an affine surjective étale cover. The natural simply
transitive radical action and the supplied surjective étale singleton
sheaf condition then produce a smooth affine surjective model representing
the actual Levi presheaf.

For an arbitrary base, a model of a changed-base parabolic represents the
restriction of the original presheaf through the canonical base-change
isomorphism. Models on the standard affine open cover therefore glue by
the published Zariski local-representation theorem. The resulting model
retains affine, smooth and surjective structure morphism.

The sheaf conditions and existence of the affine local models are explicit
parameters of the corresponding constructions. This module is an internal
step toward the torsor theorem; it does not assert them as assumptions of
that final target. The geometric source is Conrad, *Reductive group schemes*
(2014), Corollary 5.4.6, p.178, source identifier
`conrad-2014-reductive-group-schemes`.
