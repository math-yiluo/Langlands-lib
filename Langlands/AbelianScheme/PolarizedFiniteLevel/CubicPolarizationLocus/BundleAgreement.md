# The closed locus of line-bundle agreement modulo a base twist

`exists_normalizedBundle_agreementLocus` constructs a closed subscheme of the base of an abelian scheme. A test factors through it exactly when the two given bundles on the changed abelian scheme differ by tensoring with a bundle from the test base.

The proof places the two normalizations in the rigidified family over the identity parameter and applies `rigidifiedClassesEqualizerClosed`. After changing the test, the forgetful classes are the pullback to the parameter-first product of the normalized classes on the actual changed abelian scheme. The product symmetry makes that pullback injective. The rigidified classes agree exactly when their forgetful classes agree, by rigidified transport along a carrier isomorphism for a split section. The equivalence in `normalizedBundleClass_eq_iff` provides the base twist.

This follows the normalized sheaf comparison in Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), Proposition 6.11, printed p. 123 (PDF p. 136), source `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`, SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.
