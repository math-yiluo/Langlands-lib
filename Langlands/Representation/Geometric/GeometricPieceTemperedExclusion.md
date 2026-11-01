# Tempered leading-character exclusion in a reversed geometric piece

Workers 526, 828, 359 and 430 contributed the actual reflection,
character-extraction, coordinate and source-twist route. The final analytic
and finite-real-algebra inputs are `RefinedUpperTemperedConeProof` and
`ReversedCoarseProjectionWeylRigidityProof`, with their own documented
provenance. This module composes those results internally.

`Langlands.Geometric.geometricPiece_tempered_leading_implies_reverse`
fixes an actual smooth analytically tempered representation `A` of a product
Levi `B`, one Borel Haar measure on its quotient by the full centre, a
strictly decreasing coarse real vector `t`, and a raw minimal representative
`v` from `B` to `B.reverse`. The source and target intersection Levis
are identified with the actual refinements `S` and `R`. A uniform
generalized character `chi` of the actual geometric piece of twisted `A`
has leading real coordinates `B.reverse.size j * t j.rev`.
The conclusion is `v = B.reversePermutation.symm`.

The untwisted projection theorem first produces an open fine generalized
character of the actual source normalized upper refined Jacquet module,
with real coordinates `x`. Put
`xd a = x (blockIndex fine a) / fine.size (blockIndex fine a)`.
The analytic upper-cone theorem puts this divided, repeated diagonal
vector in the closed positive root cone within each original source
block. The actual flattened index identities convert the analytic
theorem's coordinates into the displayed `xd`.

The same untwisted projection gives the coarse sums of `xd` plus the
source coarse twist. For raw rigidity use
`u = B.reversePermutation * v`, so
`u.symm a = v.symm (B.reversePermutation.symm a)`.
The identity `reversePermutation_symm_index` identifies the reversed
target block `j` with original block `j.rev`, including its size.
Choosing the reversed label first avoids dependent casts and supplies
exactly the coarse-sum hypotheses of raw rigidity. That theorem forces
the stated inverse block reversal. No involutivity of reversal or
minimality of `u` from `B` to `B` is used.

The statement retains arbitrary rank, including zero, arbitrary central
shifts of `t`, zero cone coordinates, and independent field and source
universes. The coarse character need not have open kernel; the input is
the actual common-power generalized occurrence. Temperedness supplies
admissibility, and no irreducibility, support, scalar action,
semisimplicity or finite-carrier-dimension premise is added.
