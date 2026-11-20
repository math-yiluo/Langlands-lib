# Nested averaging of same-class canonical Jacquet lifts

Worker 813 assembled this proof using Worker 209’s carried uniqueness
argument and Worker 938’s published `blockStableImageAverageBridge`.

`Langlands.Jacquet.blockStableImageNestedAverage.{uF,uV}` proves
`BlockStableImageNestedAverageClause F T B V` from
`CanonicalLiftCompatibilityStatement`. It uses the supplied p-adic field and
topological data, every rank and block shape, and an admissible complex
representation in an independent universe. This includes rank zero, empty
and one-block shapes, and the zero representation. For the supplied compact
open subgroups `K1 ≤ K0` with block Iwahori factorization, it compares two
actual stable-image representatives of the same ambient upper Jacquet class.
The equality is in `V`, with `Compact.averageMap` taken over `K0`.

The proof uses `blockStableImageTupleIndependence` at `K0` to put the second
representative in the stable image for the first representative’s tuple.
The underlying `K0`-fixed vector is the same. The shared-tuple theorem
`averageMap_eq_of_stableImage_mk_eq` then applies the published averaging
bridge. Its first component places the averaged vector in the `K0` stable
image. For its second component, `fixedJacquetMap` gives the larger
representative a class fixed by `K0 ∩ M` under the unnormalized descended
Levi action. The same-class premise gives this fixedness for the smaller
representative’s class. The bridge therefore gives the averaged vector the
class of the larger representative.

The uniqueness step compares these two `K0`-fixed vectors. Their difference
belongs to the stable image by linearity and to the kernel of
`fixedJacquetMap` by equality of classes. `blockPowerKernel_eq_jacquetKernel`
identifies this kernel with the supremum of the power kernels.
`powerKernelSup_isCompl_stableImage` makes those kernels’ supremum disjoint
from the stable image, so the difference is zero. Admissibility provides
the finite dimension needed here on the `K0`-fixed space. This argument uses
injectivity on the stable image to compare the two given representatives.

`Langlands.Jacquet.blockCanonicalLiftCompatibility` pairs the published
tuple-independence proof with the nested averaging theorem to prove
`BlockCanonicalLiftCompatibilityStatement F T B V`.

The source for this block `GL_n` formulation is Casselman’s Lemma III.5.7
on page 7, with the stable complement discussed after Lemma III.5.4 on page
6. The specialization uses the Library’s factorization predicate, which
includes conjugation containments for weakly contracting tuples. The proof
works directly with the normalized finite-orbit average and all-power stable
image. The remark after III.5.7 records the withdrawn argument for general
Noetherian coefficient rings. The coefficient field here is `ℂ`. The
registered source is `casselman-2019-jacquet-module`,
revision April 29, 2019, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
[Casselman, Chapter III](https://personal.math.ubc.ca/~cass/research/pdf/Jacquet.pdf#page=7).
