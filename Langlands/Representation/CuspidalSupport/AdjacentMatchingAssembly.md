# Conditional adjacent factor matching assembly

This internal derived module reuses the smooth objects for induction
inside refined blocks from
[RefinedInnerInductionObjects](../Parabolic/RefinedInnerInductionObjects.md)
and assembles adjacent factor matching from two explicit theorem inputs.
Its imported construction entry is
`Langlands.CuspidalSupport.refinedInnerInductionObjects`. Its final
conditional theorem is
`Langlands.CuspidalSupport.adjacentBlockSwap_of_twoBlock_and_length`.
It assumes:

- `TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF,uV,uV}`, the full
  published associated two-block matching proposition, for all primes,
  p-adic fields, topological data, positive ranks, shapes and actual
  irreducible cuspidal inducing representations in the indicated universes.
- For every prime `p`, `F : PadicField.{uF} p`, topological data `T` and
  natural rank `n`, `CuspidalInductionLengthTheorem.{uF,uV} F T n`.
  This is the full published proposition, including rank zero, finite
  group-module length and the factorial bound on composition length.

The conclusion is the unchanged
`AdjacentBlockSwapCuspidalInductionFactorsTheorem.{uF,uV,uW}`.
Field, source and target carrier universes remain independent. The module
proves neither input and supplies a conditional prerequisite, so it does
not complete the host proof task. The length input retains its complete
published telescope even though this assembly uses only its finite-length
conjunct at positive rank.

The source and reversed inner tensors are the actual objects constructed in
`AdjacentMergedTensor`, over the common shape formed by merging the adjacent
blocks. `adjacentInnerInductions_matching` uses their actual transport
equivalence to prove association. At the merged slot, whose refinement has
two blocks, it applies the two-block input. At every other slot, whose
refinement has one block, it applies the published
`associatedCuspidalInductionFactors_of_length_lt_two`. Inner irreducibility
and Levi cuspidality come from `adjacentInnerTensors_cuspidal`; no inner
matching assumption is added.

`refinedInnerInductionObjects` takes an outer block shape `D`, a refinement
`S` and actual smooth tensor factors `C`. At each block `m` it bundles
`RefinedInductionTensor.blockRepresentations F T D S C m` as a smooth
representation of `GL_(D.size m)(F)`, using
`T.isSmooth_normalizedParabolicInduced`. Its carrier universe is
`max uF uV`, while the input factors have carrier universe `uV`. The
construction requires no matching, admissibility or length hypothesis.

`adjacentInnerExternalTensors_matching` uses these smooth objects for both
actual inner induced families. `normalizedInductionAdmissibility` applies to each inner
cuspidal tensor, separately on both sides. The published
`FiniteTensor.padicExternalTensorFactors` then combines the inner matches
over the merged Levi. Positive ambient rank and both admissibility inputs
are supplied explicitly.

`supercuspidalProductInduced_finiteLength` applies the pointwise full length
input to the actual global external tensor. `glCuspidalTensor` supplies its
irreducibility and Levi cuspidality. In
`canonicalAdjacentProducts_of_twoBlock_and_length`, this gives finite length
for both the original global product and its adjacent reordering.

The private `matchingThroughStages` helper transfers these two lengths along
the actual stages equivalences using their surjective intertwiners. It
applies `normalizedInductionFactorMatchingTheorem` to the tensor match and
both outer length proofs. Finally,
`haveSameJordanHolderFactors_transport` transports the resulting series
through both inverse stages equivalences, retaining matching factors and
their multiplicities. The source stages construction first identifies the
generic ordered-refinement tensor family with `adjacentInnerTensor` by
reflexivity, and transports the stages equivalence along this equality.
This equality transport changes no representation or normalization.

The final declaration applies the published
`adjacentBlockSwap_of_canonicalProducts`. That reduction uses canonical
cuspidal tensor factorization and actual normalized induction equivalences
to recover the full adjacent target, including an independently sized
target carrier. The assembly assumes neither the parent association
theorem nor the cuspidal association equivalence.

Provenance is internal and derived: the module composes the published
actual tensor and stages constructions, the one-block comparison,
normalized admissibility, finite external tensor matching, normalized
induction matching, finite-length transport and canonical tensor reduction.
It transcribes no additional theorem from the literature. The two full
external theorem obligations remain explicit in the Lean declarations and
in this description.
