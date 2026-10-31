# Jordan–Hölder matching for finite external tensors

The theorem `Langlands.FiniteTensor.padicExternalTensorFactors` proves the
published `PadicExternalTensorFactorsTheorem.{uF,uV,uW}` exactly. For a
positive-rank block shape over a p-adic field with the supplied compatible
topology, factorwise `HaveSameJordanHolderFactors` for two admissible smooth
families implies that predicate for their actual `blockTensor` actions on the
same block Levi. Field and the two families' carrier universes remain
independent. The target and its imported definitions are unchanged.

Worker 161 implements this proof. The tensor-filtration construction in
`Langlands.Representation.Tensor.Filtration` is by Worker 439. All other
mathematical inputs are imported by their Library names.

## Actual series transport

The shared helper `Langlands.haveSameJordanHolderFactors_transport` in
[`JordanHolderTransportProof`](../Filtration/JordanHolderTransportProof.md)
uses `jordanHolderSeriesTransport` on each side and composes the resulting
graded equivalences with the supplied factor permutation. This is the former
private `matching_transport` helper, relocated without changing its hypotheses
or proof. The pullback helpers are shared in
[`FactorMatchingPullback`](../Filtration/FactorMatchingPullback.md).
`filtrationComp` pulls each actual invariant subspace
back along a surjective group homomorphism, using
`subrepresentationCompOrderIso`. Its graded quotient is equivariantly
identified by `gradedComp` with the pulled-back original quotient.
`matching_comp` preserves the simple-factor conditions and permutation under
this construction. `matching_of_comp` applies the inverse group isomorphism
and cancels the two pullbacks. These operations retain actual subspaces,
quotient actions, and multiplicities.

`tensorEquiv` is the tensor product of two equivariant linear equivalences.
`tensor_right_matching_of_graded` applies `gradedJordanHolderRefinement` to
`s.tensorRight B` and the corresponding filtration on the other side.
It transports each assumed graded matching through the actual
`tensorRightGradedEquiv`. The supplied filtration length may be zero, and
its graded pieces need not be simple or nonzero.

## Admissible simple factors and binary matching

`graded_admissible` first applies admissibility inheritance along the
inclusion of the upper step, then applies the published surjective-intertwiner
lemma to the actual graded projection. The quotient argument uses compact-open
cofinality. `compactOpen_cofinal` derives this property for locally compact,
Hausdorff, totally disconnected groups from
`Hecke.TestFunction.commonCompactOpenBiInvariance` with an empty test family.

`binary_irreducible` realizes a binary external tensor as a finite external
tensor indexed by the sum of two singleton types. Admissible Schur supplies
scalar self-intertwiners, so `isIrreducible_external` applies. The indexed group
is reached by a surjective map from the ordinary product group. The inverse
of `PiTensorProduct.tmulEquivDep`, followed by the two singleton equivalences,
identifies the tensor carrier with the ordinary binary tensor. Its formula on
pure tensors proves equivariance, and the invariant-subspace order isomorphism
transfers irreducibility. `binary_simple_matching` combines this with the
published length-one matching theorem and the tensor of two given equivalences.

`simple_left_matching` fixes a simple admissible left factor and uses the
supplied matching composition series for the right factor. After pulling the
series back by the second projection, it applies the right tensor filtration
with the left factor fixed. Each graded comparison comes from
`binary_simple_matching` and the actual tensor commutor. Another commutor
returns to the original order of factors. `binary_matching` applies the same
refinement argument to the supplied left composition series, pulled back by
the first projection. Its graded matching is `simple_left_matching`.
Thus both given factor permutations enter actual graded refinement, including
all multiplicities. No chosen lists of constituents replace the filtrations.

These binary helpers require admissibility only of the first family: the
second family's simple pieces are supplied by its matching composition series
and equivalent to the corresponding pieces of the first family. The final
published target retains both admissibility hypotheses exactly.

## Finite induction and p-adic specialization

`finite_matching` inducts on a nonempty index set `Fin (r + 1)`. The base case
uses `singletonEquiv` and reflection of matching along the singleton evaluation
group isomorphism. The induction step applies the hypothesis to the tail,
obtains its admissibility from `isAdmissible_external`, applies
`binary_matching` to the head and tail, and uses `headTailEquiv` to return to
the actual dependent external tensor. Locally profinite hypotheses pass to
the finite product of tail groups.

For the final specialization, the field topology comes from `T` and the GL
instances are `T.generalLinearTopologicalGroup`, `T.generalLinearT2Space`, and
`T.generalLinearLocallyCompactSpace`. The private total-disconnectedness
helpers use the valuation topology and the continuous injective inclusion of
matrix units into the matrix space. This repeats the topological argument in
`LeviAdmissibleFactorizationProof`, without using or reproving its factorization
theorem. Positive rank gives positive block length; replacing that length by
its predecessor plus one permits finite induction. `blockTensor` is the
published abbreviation for the actual `FiniteTensor.external` action.

Zero or reducible source factors are allowed. Their finite composition series
come from the matching hypothesis. Tensor image filtrations can have repeated
steps and zero graded pieces, and both refinement layers preserve that case.
No nonzero, finite-dimensional, irreducible-source, or additional finite-length
hypotheses are imposed.

## Provenance

This is a derived result from tensor exactness over complex vector spaces,
admissibility inheritance, Schur's lemma, and admissible external-tensor
irreducibility. It is not a verbatim theorem in the cited literature.
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), sections 2.2 and 2.7, printed pp.446–447 (PDF pages 7–8), supplies the
GL block-Levi and external tensor setting. Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Flath, *Decomposition of representations into tensor products* (1979),
Theorem 1(1.1), printed pp.179–180 (Corvallis Part I PDF pages 175–176),
supplies the irreducibility context. Registered source:
`flath-1979-tensor-products`, volume SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
These originals were read on 2026-10-24; no source-specific retained errata
note was found. The implemented proof route is the actual filtration
construction and two refinements described above.
