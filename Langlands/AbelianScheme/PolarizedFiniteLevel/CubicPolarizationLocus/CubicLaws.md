# Cubic diagonal bundles under dual comparison

`cubicDiagonalBundle` is the actual tensor cube of the diagonal Poincaré bundle of a homomorphism to a witnessed dual. For a polarization over a locally noetherian base the ordinary Mumford map of this cube is six times that homomorphism. The proof combines `polarizationDiagonalMumford` with the power law and evaluation independence for `lineBundleMumford`.

The same bundle construction is compatible with arbitrary base change and with isomorphisms of abelian schemes. Both compatibilities use the corresponding actual Poincaré isomorphisms and the tensor power comparison. They transfer an `ExistsCubicPolarization` witness along an abelian-scheme isomorphism, or replace its chosen presentation of the dual on the same abelian scheme. The transported polarization and degree use the published isomorphism transport results.

The diagonal calculation is Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), Proposition 6.10, printed p. 121 (PDF p. 134), source `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`, SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.
