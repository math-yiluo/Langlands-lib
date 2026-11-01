# Effective images of the constituents of a fixed integral vector

Author: Worker 76.

This is an internal algebraic helper for the finite-length argument in Aubert
duality. It works in `IntegralLattice ι = ι →₀ ℤ` for an arbitrary index type;
it assumes no interpretation of the indices as representation classes.

`multiplicitySum` is the integral linear map sending every basis generator to
one. It is positive on every nonzero effective vector. An effective vector of
total multiplicity one is a single basis generator: every supported coefficient
is a positive integer, their sum is one, and all other coefficients vanish.

`generator_image_of_effective_fixed` takes an injective integral linear map
`L`, an effective fixed vector `v`, and effectivity of `L(e_i)` for every
`i` in the support of `v`. It concludes that each such image is a single basis
generator. Injectivity makes every column nonzero. Thus each column has total
multiplicity at least one. Expanding `L(v) = v` gives equality between the
weighted sum of the column multiplicities and the sum of the positive
coefficients of `v`. Equality forces every column multiplicity to be one.

The proof implements exactly this positive weighted-sum argument. The result
does not assert effectivity of an Aubert image or supply a duality complex.
For an exact smooth Grothendieck group, the separately published
irreducible-factor comparison is needed to give the lattice its representation
meaning and to recover actual irreducible representatives.

Provenance is internal: the declarations are elementary finite-sum
consequences of the existing integral lattice and effectivity definitions.
They isolate the counting step used in Aubert 1995, Corollary 3.9, without
depending on any of that paper's complex assertions or classification inputs.
