# Pair \(L\)-factors of isomorphic irreducible real standard modules

The theorem `realStandardIntertwinerPairL` has type
`RealStandardIntertwinerPairLStatement`. For two rank-matched irreducible
real standard modules and a nonzero compact and Lie intertwiner, it gives
equality of the pair \(L\)-factor denominators against every real block list,
in both slots.

The proof applies `realStandardEllipticCartanReduction` to
`RealStandardEllipticCartan.realStandardEllipticCartanComparison`. The
comparison gives common counts of induced blocks and real characters and
equal finite Cartan numerators for enumerations of the positive-weight
lists. The reduction uses the numerators to recover the induced weights
and exponents and the real character parities and exponents up to
permutation.

The proof passes this uniqueness result to
`realStandardIntertwinerPairLReduction`. That reduction splits induced
blocks of weight zero into two real characters and replaces negative
weights by their absolute values. The module identifications transport the
intertwiner to the normalized lists. Irreducibility and the nonzero
hypothesis make it a bijection there. Uniqueness gives a permutation of
those lists. The pair factors are invariant under normalization and
permutation, so taking denominators gives both equalities.
