# Descent along an fppf kernel pair

`Langlands.AlgebraicGeometry.QuasiAffineApproximation.exists_fac_of_kernelPair` is the shared helper previously in `QuasiAffineApproximation.QuotientSpace`.

For a flat, locally finitely presented, surjective morphism `q : U' ⟶ M` with kernel pair `IsPullback t' s' q q`, a map from the functor of points of `U'` to an fppf sheaf that agrees along `t'` and `s'` factors through `q`. The scheme-sheaf map of `q` is locally surjective and hence an effective epimorphism. The kernel-pair lifting property verifies the compatibility needed for its descent map.

The statement, universe, namespace and proof are unchanged. Both the quasi-affine quotient construction and the locally noetherian quotient reduction import this helper.
