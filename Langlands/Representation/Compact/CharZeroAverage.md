# Finite-orbit compact averaging over characteristic-zero fields

Worker 1643 generalizes the published finite-orbit construction of Worker 5
(`Langlands.Representation.Compact.FiniteMean`, `Definitions`, and
`ProjectionProof`) from complex coefficients to an arbitrary characteristic-zero
field. This is internal algebraic support for the proof following Vignéras 1996,
Chapter I §7, printed pages 54–62, registered source
`provided-74667a7cddb3bdafff85f01c658605ce7d929f6da73950d79457c46bcd761dd4`.
The counting proof is inherited from the published construction; it only uses
that each positive finite cardinality is invertible in the coefficient field.
No topology is imposed on that field or on a representation carrier.

The field, group, source carrier, target carrier, and finite indexing types have
independent universes. `finiteMean` normalizes a finite sum by the indexing
cardinality. `finiteMean_comp` uses equal-sized fibers of an equivariant map to
a transitive finite set. `orbitMean` averages the distinct orbit vectors. Its
total definition uses `Nat.card` and `finsum`; its linearity, invariance, and
identity properties are asserted with finite-orbit hypotheses. Intertwiners
preserve orbit means. Addition follows by the orbit of a pair, and homogeneity
follows by the scalar-multiplication intertwiner. Translating the initial vector
leaves its orbit and its mean unchanged.

For a smooth representation of a topological group and a specified compact open
subgroup `K`, each restricted orbit is finite by the orbit-stabilizer equivalence
and compactness of the quotient by an open stabilizer. `averageMap` is the
resulting linear projection onto the existing submodule `fixedVectors ρ K`.
It is the identity on that submodule and commutes with intertwiners. The
codomain-restricted map `fixedProjection` is a retraction and satisfies
`fixedProjection_apply_rho`: it is unchanged by applying any element of `K` to
its argument. Averaging a preimage proves `fixedVectorMap_surjective` for every
surjective intertwiner of smooth representations.

`fixedExtension` composes a functional on the fixed vectors with this projection.
It restricts to the original functional and is fixed by `K` in the algebraic dual
representation, hence is smooth. The dual-action proof uses invariance of the
projection under the inverse of the acting element. There are no measure,
local compactness, unimodularity, admissibility, or irreducibility hypotheses.
The construction establishes the compact-open averaging tools; the full
injectivity and projectivity theorem needs further arguments.
