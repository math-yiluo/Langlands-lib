# The arithmetic Hilbert norm-residue pairing

Let `F` be a nonarchimedean local field, let `n` be positive, and let
`hζ : (primitiveRoots n F).Nonempty`. The value `hilbertNormResidue hζ a b`
for `a b : Fˣ` lies in `rootsOfUnity n F`. Its first argument goes into
arithmetic local reciprocity. Its second argument determines the radical
splitting field `R = KummerNorm.radicalField F n (b : F)`. The definition
applies `kummerCharacter` on `Gal(R/F)` to `arithmeticFiniteArtin F R a`.
The primitive-root hypothesis makes `R/F` abelian Galois by
`isAbelianGalois_radicalField`. The construction includes equal and mixed
characteristic, `n = 1`, and all degrees of the radical splitting field,
including degree one when `b` is already an `n`-th power in `F`.

For any root `β` of `X ^ n - C (b : F)` in `R`,
`algebraMap_hilbertNormResidue_radicalField` evaluates the image of the
symbol in `R` as `(arithmeticFiniteArtin F R a) β / β`. The computation is
independent of which root is used because `kummerCharacter_eq` identifies
the characters on different roots of the same unit.

More generally, if `E/F` is finite abelian Galois and `β ^ n = b` in `E`,
then `hilbertNormResidue_eq_kummerCharacter` identifies the symbol in
`rootsOfUnity n F` with evaluation of the character on
`arithmeticFiniteArtin F E a`. One root together with the base roots of
unity splits the binomial in `E`, so `Polynomial.IsSplittingField.lift`
gives an embedding of `R` into `E`. The arithmetic Artin map is compatible
with restriction in this tower. The Kummer character is also compatible
with restriction, and root independence replaces the image of the chosen
root of `R` with `β`.

The theorem `algebraMap_hilbertNormResidue` writes this common-extension
evaluation as `(arithmeticFiniteArtin F E a) β / β` after mapping the
symbol to `E`. Thus one Artin automorphism of `E` can be used for every
unit whose radical is in `E`. In an unramified extension, the theorem
`algebraMap_hilbertNormResidue_uniformizer` uses
`arithmeticFiniteArtin_of_normalizedUnitOrder_eq_one` to compute the
quotient for a uniformizer using arithmetic Frobenius.

## Source

John Milnor, *Introduction to Algebraic K-Theory* (1971), §15,
Remarks 15.9–15.10, printed pp. 151–152 (PDF pp. 153–154), gives the
reciprocity normalization and the action on an `n`-th root of the second
argument. The source ID is `milnor-1971-introduction-algebraic-k-theory`
and the retained file has SHA-256
`cf793856c54a428593940eef304c4cec35478966b8b8525ccfc153473f3d157a`.
