# The Mumford map of the actual cubic diagonal bundle

`cubicBundleMumford` proves `CubicBundleMumfordStatement`: for every existing
prerequisite package and polarized finite-level datum over any field, the
actual tensor cube `a.cubicBundle` admits normalization data for which its
Mumford scheme map is the underlying map of `6 • a.polarization`.
The conclusion uses the datum's existing dual scheme. There is no
algebraic-closure, characteristic, positivity, or extra geometric hypothesis.

The proof first establishes a general comparison for a one-point base.
`normalizedInverse_isoClass` uses the normalization evaluation and the
triviality of every base line-bundle class to show that the auxiliary
inverse has class `[L]⁻¹`. Consequently,
`familyPointClass_mumfordFamily_of_unique` identifies the class of the
actual normalized Mumford family at two points `u,v` as
`[(uv)*L] [u*L]⁻¹ [v*L]⁻¹`. The comparison is about ordinary isomorphism
classes, so the particular normalization inverse and evaluation do not affect it.

`isoClass_tensorPow` proves by induction that the actual sheaf tensor power
has class `[L]^k`, including `k = 0`.
`familyPointClass_poincareFamily_pow_left` extends the published
multiplicativity of Poincaré pullback in the dual variable to every
nonnegative power. At zero, multiplicativity makes the class idempotent,
and cancellation in the class group makes it the identity.

`familyPointClass_mumfordSchemeMap_of_unique` transfers the Mumford family
calculation to the actual Poincaré pullback along its classifying scheme
map. The general result
`mumfordSchemeMapOfLineBundle_eq_pow_of_isoClass` then shows that
`[L'] = [L]^k` implies that the actual Mumford map of `L'` is the
`k`-th pointwise power of the actual Mumford map of `L`, for every supplied
choice of their normalization data. It compares their Poincaré classes at
the tautological projections, obtains an ordinary bundle isomorphism,
and upgrades that isomorphism to a rigidified one using the unit-section
retraction. The published injectivity of Poincaré classification gives
equality of the actual maps.

For the final specialization, `polarizationDiagonalMumford` supplies
normalization data for `a.canonicalBundle` and identifies its Mumford
map with `2 • a.polarization`. Actual tensor inverses supply the cubic
normalization data. The comparison with exponent three identifies its
Mumford map with the cube of that map. `groupHom_nsmul_hom` identifies
addition of abelian-scheme homomorphisms with pointwise multiplication
of their parameter maps, and `3 • (2 • polarization) = 6 • polarization`
finishes the proof.

This is an internal derivation from the published diagonal Mumford theorem,
Poincaré class multiplicativity, and line-bundle normalization and
classification. The proof does not assert ampleness, the degree formula,
or any cohomology vanishing or dimension. Those remain separate inputs to
`CubicFibreCohomologyStatement`.
