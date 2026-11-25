# Spherical spectra of subquotients of products of spherical blocks

`Langlands.Unramified.ProductInducedSpectrum.exists_hasSphericalSpectrum_of_isSubquotientOf_productInduced`
computes the spectrum of a spherical subquotient of a normalized block induction
for a p-adic field `F`. The input objects `σ i` for `GL_(m i + 1)(F)` have
spherical spectra `s i`. The block sizes sum to `r + 1`. The input object `A`
for `GL_(r+1)(F)` has a nonzero vector fixed by `GL_(r+1)(O_F)` and is a
subquotient of the normalized induction of the `σ i` from the standard upper
block parabolic. The theorem supplies a spherical spectrum `t` of `A` with
underlying multiset `∑ i, (s i : Multiset ℂˣ)`. The carriers of the block
objects and of `A` can lie in different universes.

In `HasSphericalSpectrum F π s`, a tuple enumerating `s` induces an unramified
principal series having `π` as a spherical subquotient. The convention
`IsSubquotientOf ρ π` places the larger representation first.

## Proof

1. Choose the tuples `z i` from the spectra of the `σ i`. Each `σ i` is a
   subquotient of `principalSeriesOfTuple F (z i)`.
2. Apply `isSubquotientOf_normalizedProductInduced` to these subquotients. For
   each block write the subquotient as a quotient of a subrepresentation. The
   inclusions of the subrepresentations induce an injection by
   `FiniteTensor.piTensorMap_injective` and `normalizedParabolicInducedMap_injective`.
   The quotient maps induce a surjection by `normalizedProductInducedMap_surjective`.
   Smoothness of the subrepresentations follows from `isSmooth_of_injective`.
   The inverse of `Classification.JuxtaposedShuffle.rangeEquivOfInjective` followed
   by the induced surjection exhibits the required quotient of the image of the
   induced injection.
3. In `exists_principalSeries_equiv_productInduced`, refine each block by its
   Borel shape. The inducing characters on `GL_1(F)` act on `ℂ` and are smooth
   because `isOpen_ker_determinantUnramifiedCharacter` gives an open kernel.
   Reindex the tuples along `flattenBlockEquiv` and the equality of the flattened
   length with `r + 1` to get a tuple `Z`. Reindexing the sums of singletons gives
   `(Eigenvalues.ofTuple Z : Multiset ℂˣ) = ∑ i, (Eigenvalues.ofTuple (z i) : Multiset ℂˣ)`.
4. Compare the Borel induction of `Z` with induction from the flattened shape
   by transporting the shapes and character families along their equalities.
   Apply `Parabolic.flattenedProductInducedEquiv` to get the iterated induction.
   The inner inductions are the block principal series, and
   `normalizedProductInducedEquiv` applies those blockwise equivalences.
5. Compose the two subquotient relations by `WeylBranchPieces.IsSubquotient.trans`
   and transport the larger representation to `principalSeriesOfTuple F Z`
   by `WeylBranchPieces.IsSubquotient.of_equiv_left`. The fixed-vector assumption
   now supplies `HasSphericalSpectrum F A (Eigenvalues.ofTuple Z)`.

## Provenance

This is the local calculation preceding display (1) in the proof of Jacquet
and Shalika's Theorem (4.4). The sum of the eigenvalue multisets represents the
semisimple conjugacy class of the direct sum of the block parameters. The local
lemma uses exactness and induction in stages. Its application in
`CuspidalInducingDataRigidityReduction` uses uniqueness of the spherical spectrum
of the supplied common subquotient to obtain display (1).

- H. Jacquet and J. A. Shalika, *On Euler products and the classification of
  automorphic forms II*, Amer. J. Math. 103 (1981), proof of Theorem (4.4),
  printed p. 809 (registered `jacquet-shalika-1981-euler-ii`, PDF p. 34).
