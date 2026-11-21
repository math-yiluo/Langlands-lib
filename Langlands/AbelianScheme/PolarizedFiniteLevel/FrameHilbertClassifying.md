# Finite-type classifying family for frame-normalized cubic embeddings

`CubicFrameClassifyingFamily g d n m` records a noetherian scheme locally
of finite type over `Spec (ULift ℤ)`, a flat and locally finitely presented
closed family in its relative projective `m`-space, and integral projective
points indexed by full-level coefficient tuples. For any frame embedding
of a datum of dimension `g` and polarization degree `d²`, there is a unique
map to the base pulling the ideal and the indexed points back to those of
the embedded datum. This property only requires classifying families from
actual frame embeddings. The ambient universal family is not required to
be a polarized abelian scheme.

`nonempty_cubicFrameClassifyingFamily` constructs such a family for `n ≠ 0`.
It takes the published Hilbert family for the native `𝒪(1)` on integral
projective `m`-space. Use only its open piece for `cubicHilbertPolynomial g d`,
and iterate relative projective `m`-space a finite number of times to adjoin
one point for each level tuple. The open piece is H-projective over the
base by the Hilbert-family theorem, and each iteration is proper over the
previous stage. The ambient base is therefore proper, in particular compact
and locally of finite type over the noetherian affine base. The universal
ideal inherits flatness and local finite presentation.

For a frame embedding over a scheme `T`, the closed-immersion kernel
transports along `isoPullbackSpec` into the shape classified by the Hilbert
scheme. The classifying map to the full Hilbert scheme lands in the fixed
polynomial piece: at each point of `T` restrict the family along its residue
field map. The restricted family is still the image of a frame embedding,
and on every further algebraically closed field base change the section
rank equals the fixed polynomial in every positive exponent by
`Datum.IsFrameEmbedding.geomFibreH0Finrank_eq_cubicHilbertPolynomial`.
The affine-test criterion for the Hilbert piece gives the required range
inclusion. The lift through that open immersion is unique, and the
universal property of the iteration adds the indexed points uniquely.

This is a derived specialization of the published Hilbert-family and
relative-projective-space interfaces. The use of a fixed Hilbert polynomial
for the cubic embedding with level points corresponds to the ambient
construction in Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*,
3rd ed., printed p. 131 (Proposition 7.3 and its setup). This module supplies
the ambient family, not the locally closed frame locus of that proposition.
