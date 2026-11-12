# Compactness from bounded-root coverage after Galois scalar extension

This internal reduction connects compact representatives for bounded-root
parabolic products over a finite Galois extension to compact principal
representatives over the original number field. All fields and group schemes
use the same arbitrary universe, and the adelic carriers, all-character
norm-one subgroups and principal maps are the existing Library objects.

`scalarExtensionNormOneMap` is the continuous homomorphism obtained by
composing the norm-one map of the actual affine Weil unit with the canonical
adelic Weil comparison. Its composite with the upper principal quotient is
exactly the published `scalarExtensionQuotientMap`.

The theorem
`hasCompactNormOneRationalCover_of_scalarExtension_representatives` assumes
one compact subset of the upper norm-one group meeting the upper-field
principal coset of every scalar-extended source point. Its image in the upper
rational quotient is compact. Each point in the image of the source quotient
belongs to that compact set, because multiplication by an upper rational point
preserves the upper quotient class. The upper quotient is Hausdorff, so the
closure of the image is compact. The published closed embedding of the actual
scalar-extension quotients then pulls this compactness back to the source.
The published local compactness argument reconstructs a compact set of
principal representatives in the original norm-one group.

`HasBoundedRootScalarExtensionCover` states the precise additional coverage
condition used here: there are a bound \(b\geq1\) and one compact upper ambient
factor \(C\) such that every scalar-extended source norm-one point has an
upper-field rational translate in
`boundedRootParabolicProduct`. This ordered product consists of the canonical
minimal standard parabolic's own full norm-one subgroup, the full torus's
ambient norm-one two-sided simple-root box, and \(C\).

If the upper group is connected reductive, the chosen torus is both maximal
split and maximal as a torus, and the cocharacter is generic, the theorem
`hasCompactNormOneRationalCover_of_boundedRootScalarExtensionCover` constructs
compact principal representatives over the original field from that condition.
The bounded-product theorem supplies a compact set of upper norm-one
representatives. For each source point, the coverage condition supplies a
rational translate in the product, and the bounded-product theorem supplies
a second rational translate in the compact representative set. Their product
is the upper rational point required by the first pullback theorem.

The final theorem
`FiniteGaloisSplitMaximalModel.hasCompactNormOneRationalCover_of_boundedRootCover`
uses the published actual splitting bundle. Its existing fields supply the
finite Galois extension, split maximal torus and connected reductivity after
base change. Maximality of a split torus implies maximal splitness. Finite
dimensionality gives the upper number-field structure. Thus a generic
cocharacter and the displayed bounded-root coverage condition are the only
additional mathematical inputs to this specialization.

The provenance is internal composition of the imported Library proofs. This
module proves a conditional reduction and does not prove bounded-root
coverage, uniform root estimates, the split fundamental-set theorem, or
`CentralSplitCompactQuotientStatement`.
