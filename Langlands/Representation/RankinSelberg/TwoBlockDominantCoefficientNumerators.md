# Finite numerators for actual equal-rank coefficient images

This internal deduction specializes `TwoBlockDominantNumeratorExtraction` to
actual coefficient images. It uses the published `equalRankSliceSupport`,
`DualModels` and `DualWhittakerType` results to discharge the original and
dual lower support bounds. The two polynomial-cleared block equations and
the lower Fourier coefficient law remain explicit premises.

`equalRankDualSliceCoefficient` is the actual `equalRankSliceCoefficient`
for the inverse-transpose pair, the character `ψ.scale (-1)`, the given
quotient measure, and the images of the original coefficient vectors under
`firstDualModelMap` and `secondDualModelMap`. Its row test `ΦD` is supplied.
The definition asserts no relationship between that test and an original
test `Φ`.

`equalRankDualSliceCoefficient_lowerSupport` derives full type of both
inverse-transpose representations. The published inverse-transpose theorems
reverse the character, and the character identities at `-1` give exactly
the standard and inverse-standard types at `ψ.scale (-1)`. The actual dual
model maps provide elements of the required coefficient images. Applying
`equalRankSliceSupport` to these data proves lower-bounded support for the
actual dual slice series.

`twoBlock_equalRankCoefficient_numerators` uses actual original and dual
slice series as `a` and `aD`. It applies the support theorem directly to
the original coefficient images and the preceding lemma to the dual
images, then invokes `twoBlock_cleared_numerators`. The resulting unique
Laurent polynomial has coefficient series
`(P₁ * P₂).toLaurent • a`. Its reflected numerator has coefficient series
given by the dual polynomial product acting on `aD`, with the reflected
inverse of the explicit Laurent unit `clearedProductMultiplierUnit`.
Every polynomial clearing factor remains in the conclusion.

`lowerInducedCoefficient_support` specializes the two support conclusions
to the actual two-block normalized lower induction. Full inverse-character
type of that induction follows from the imported
`lowerInduced_inverseWhittakerType`, which reverses the entire ordered
block family before applying normalized upper-induction type preservation.
The dual support theorem then derives the required inverse-transpose
type. `twoBlock_lowerInducedCoefficient_numerators` applies the general
numerator theorem to this actual lower induction. It assumes full type
only for the test representation and the individual blocks; induced
full type and both support bounds are discharged.

The field has its canonical topology and valuation data; the field and
two coefficient carriers have independent universes. The quotient measure
is supplied on its Borel structure, with the original compatibility and
unipotent right-invariance conditions retained. Full Whittaker type is
assumed for both original representations. Zero functionals and
coefficients are allowed, as is actual rank one. The two row tests are
arbitrary Schwartz–Bruhat functions. The parameter `q` is an arbitrary
nonzero complex unit, as in the imported algebraic theorem; this unit
asserts no residue-cardinality identification.

The provenance is internal composition of the named published results.
No new literature claim, coefficient equation, Fourier identity,
convergence, uniform support, rational continuation, polynomial
divisibility or final dominant-rank gamma/L theorem is asserted.
