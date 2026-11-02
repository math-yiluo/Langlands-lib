# Canonical and cubic bundle transport under polarized isomorphisms

`poincareDiagonalHomPullbackIso` is an actual line-bundle isomorphism for an
abelian-scheme homomorphism `f : A ⟶ B`, supplied duals of both schemes, and
an actual parameter map `lam : B.X ⟶ dualScheme B hB`. Pulling the diagonal
Poincaré bundle for `lam` back along `f` gives the diagonal Poincaré bundle
for `f` followed by `lam` followed by the contravariant dual map of `f`.
It works over an arbitrary base scheme and requires no polarization.

The construction forgets the rigidification in the existing defining
isomorphism `dualSchemeMapPullbackIso`. It pulls this comparison back along
the parameter-and-diagonal map from `A`. Equality of the resulting actual
scheme maps follows by the universal property of their fibre products.
The ordinary pullback composition isomorphisms identify both ends with the
two diagonal bundles.

For an actual ordinary polarized finite-level isomorphism,
`PolarizedIso.parameterMap_eq` takes the underlying parameter-scheme maps
of its polarization equation. `canonicalBundlePullbackIso` applies the
preceding diagonal comparison and this equation to construct an actual
isomorphism from the pullback of the target datum's canonical bundle to
the source datum's canonical bundle.

`PolarizedIso.cubicBundlePullbackIso` uses the actual pullback comparison for
tensor powers and the tensor cube of that canonical isomorphism to obtain
an actual isomorphism of module sheaves from the pulled-back target cubic
bundle to the source cubic bundle. No bundle-preservation isomorphism is
assumed as an additional input.

This is an internal consequence of the existing actual dual-map
classification comparison, fibre-product identities, pullback composition,
the datum's polarization equation, and tensor-power isomorphisms. It uses
no new external source assertion. The datum's original prerequisites and
per-datum dual witnesses are retained. This construction does not assert
coherence of the chosen bundle comparisons under composition, existence of
a section basis or embedding, finite-level rigidity, or moduli
representability.
