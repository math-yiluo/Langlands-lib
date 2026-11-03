# All-point norm formula for actual split-torus characters

This derived construction unit extends the intrinsic section-based parameter to
every actual rational point of an arbitrary split torus over an arbitrary-universe
nonarchimedean local field. Both characteristics and rank zero are included.
Smoothness means an open kernel for the canonical rational-point topology.

The proof uses the published intrinsic uniformizer-section representatives modulo
the actual common norm kernel. Compactness and the smooth-character norm-one
theorem imply equality of moduli for two points in the same class. The existing
positive valuation has that same kernel, so the valuation vectors agree as well.
At a section point the valuation is the embedded cocharacter; the section
logarithm and the normalized exponential identity then give the defining formula
at every point.
The definition `smoothNormalizedParameter` returns the existing normalized
parameter together with this proved all-point formula.

Uniqueness tests a purported all-point formula on all intrinsic section points
and uses pure-tensor extensionality and the actual perfect pairing. That
implication needs no smoothness assumption. Pairings against the actual valuation
image also determine every real parameter. These facts prove uniqueness without
a choice of splitting or a lattice basis.

The normalized parameter satisfies `norm = q ^ (-pair)`. The raw natural-log
parameter is separately named and equals `(-log q)` times the normalized one.
The all-point raw formula follows by cancellation of the nonzero scalar `log q`.
These are the two distinct normalizations appearing in Renard V.3.19–V.3.20;
no identification of their signs or chamber conventions is made here.

For a smooth character, the parameter is zero exactly when the complex modulus
is one at every actual point. The forward implication uses the all-point formula;
the reverse implication uses uniqueness. This file is an internal derivation from
the existing actual lattices, perfect pairing, valuation, compact-kernel argument
and intrinsic representative theorem, rather than a new torus or valuation model.
