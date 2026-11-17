# Genuine generic locus on compact carriers

The primary internal construction is
`Langlands.Plancherel.ActualCommonLeviV3.compactGenericLocus`. It expresses the
published actual `genericLocus` using bijectivity of the specified forward and
inverse-parameter reverse compact continuation operators. Its provenance is
the actual common-Levi tensor construction for Waldspurger (2003), V.3 formula
(1) and Lemma V.3.1 (printed p.295 / PDF p.61), registered source
`waldspurger-2003-plancherel`.

The two compact squares are published theorems about these particular actual
standard continuations. Each identifies its operator with the corresponding
compact operator through linear equivalences. Composition with bijections
preserves and reflects bijectivity. The two individual equivalences give
`compactGenericLocus_eq`, an unconditional equality of the two loci.
No new continuation or generic-invertibility existence is asserted. The
original field and representation-carrier universes remain independent.

`dense_unitary_regular_nonzero` applies the published density theorem for
unitary values of a nonzero rational function to the image of a nonzero
regular function. Its regularity is automatic, its rational image is nonzero
by injectivity of the fraction-field map, and its unitary value is precisely
evaluation of the original function. It covers the entire unitary group.

`hasDenseGenericLocus_of_regular_nonzero_subset` assumes one nonzero regular
function whose nonvanishing locus is contained in the compact generic locus.
The published ambient and unitary density results make this locus a nonempty
ambient open dense set with dense unitary preimage. The proved equality of
generic loci transfers the containment to the genuine actual locus, giving
all clauses of the existing `HasDenseGenericLocus`. The hypothesis that the
two compact maps are regular and invertible outside the stated zero set is
explicit; it is not supplied by this lemma. This is a density assembly helper,
not a proof of the closed V.3.1 target.
