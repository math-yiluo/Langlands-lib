# The finite Galois obstruction for a central isogeny

Let `f : G → H` be a central isogeny over a field `k`. Its
scheme-theoretic kernel is commutative because its inclusion is a
monomorphism with central image. Over a Galois coefficient field `L`,
this gives the central exact sequence on points through which the
values of a natural cocycle on `H` may be lifted.

`IsCentralIsogeny.GaloisLift` records lifts of the Galois values and
their defect in the actual kernel points. The inclusion is injective,
equivariant and central. These facts give the two-cocycle law from the
central defect calculation. A lift of every coefficient suffices to
construct this data.

For finite Galois `L/k`, `galoisLift_isMulCoboundary₂_iff` identifies
vanishing of the defect with existence of a natural lift on the same
cover. A primitive of the defect corrects the coefficients to a
crossed cocycle. The finite Galois component construction extends it
to all test schemes. Its image under `f` agrees with the original
cocycle because they have the same Galois values. Conversely, the
values of a natural lift are a crossed lift and hence give a primitive
of the defect. These are internal calculations with the actual
cover, the kernel and the specified Galois action.
