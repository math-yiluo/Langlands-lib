# Nested parabolic-orbit coefficient quotients

This internal transport identifies the actual coefficient quotient appearing
after compact induction in stages with the source intersection Jacquet quotient.
It composes `SplitStagesRetraction` and `ParabolicOrbitCoefficientComparison`;
it asserts no integral comparison or normalized natural isomorphism.

For an arbitrary commutative ring `F`, block shapes `B, C` and permutation `w`,
let `P` be `parabolicOrbitStages` and `H` be the actual orbit stabilizer in
`C.parabolic F`. The restricted retraction is the actual target Levi projection
`P → P.comap C.leviInParabolic`, with the kernel membership established by
`parabolicOrbitStages_kernel_le`. Its quotient subgroup is
`parabolicOrbitStagesQuotient`; the published
`parabolicOrbitStages_comap_section` identifies this subgroup with
`sourceParabolic F C B w⁻¹`.

The nested stabilizer is `H.subgroupOf P`, with its canonical inclusion
back into `H`. The nested intersection is its preimage along the restricted
retraction's kernel inclusion. `parabolicOrbitNestedCoefficient` restricts the
original `parabolicOrbitCoefficient` along these actual inclusions. These
are the precise groups and restrictions of the inner split-kernel integral.

For every complex representation `ρ` of `B.Levi F` and character `χ` trivial
on `sourceUnipotent F B C w`, `parabolicOrbitNestedCoefficientEquiv` identifies
the nested coefficient coinvariants with the actual
`Jacquet.Coinvariants ρ (sourceUnipotent F B C w)`.
The first equivalence removes the intermediate subgroup; the second is the
previously constructed actual orbit coefficient equivalence. Both preserve
every vector representative, so their composite and inverse do as well.
`parabolicOrbitNestedCoefficientMap` restricts the original coefficient
intertwiner via `splitStagesIntersectionMap`. Quotient induction proves
naturality for every intertwiner, with independent coefficient universes.

`parabolicOrbitStagesSection` is the actual target Levi section corestricted
to the orbit stabilizer, using `parabolicOrbitStages_section_mem`. Its
representative formula applies to every element of the full intermediate
quotient subgroup. The scalar is the original source character evaluated
at inverse conjugation followed by source Levi projection; the vector is
the source quotient class of the original action at that same coordinate.
This follows from the representative law and linearity of the quotient.

For every prime, actual finite p-adic extension and supplied compatible
topological data, the full source intersection-refinement triple identifies
the source intersection quotient with `RefinedJacquetModule B S ρ`.
`parabolicOrbitNestedRefinedCoefficientEquiv` composes the same generic
intermediate-subgroup transport with
`parabolicOrbitRefinedCoefficientEquiv`, using the actual positive
source half modulus. Its representative laws, naturality with the actual
`normalizedRefinedJacquetMap`, and full intermediate-section formula follow
by the same quotient induction and linearity arguments.

No positive-rank, minimal-permutation, smoothness, dimension or length
condition enters these algebraic transports. The field and coefficient
universes are independent. The refined quotient formula retains the source
positive half character; it does not assert cancellation with Haar factors
or identify the full intermediate action with normalized refined induction.
Those facts, the relative integral and the final categorical assembly remain
separate obligations of the normalized parabolic-orbit comparison.

The provenance is internal composition of the two named transport modules,
not a theorem quoted from literature. Bernstein–Zelevinsky section 5.16
motivates the coefficient quotient step, but this pair claims only the
explicitly implemented quotient transports.
