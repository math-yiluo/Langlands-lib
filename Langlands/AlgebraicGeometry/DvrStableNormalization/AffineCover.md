# A finite affine cover as a single affine scheme

Worker 6.

For a quasi-compact scheme `X`:

- `coverScheme X`: the disjoint union `∐ X.affineCover.finiteSubcover.X` of a finite affine open
  cover.
- `coverMap X`: the induced map `coverScheme X ⟶ X`.
- `isAffine_coverScheme`: it is affine (finite coproduct of affine schemes).
- `smooth_coverMap`: the covering map is smooth (each component is an open immersion; smoothness is
  local on the source).
- `surjective_coverMap`: the covering map is surjective.

Internal construction allowing a single application of the affine reduced fibre statement.
