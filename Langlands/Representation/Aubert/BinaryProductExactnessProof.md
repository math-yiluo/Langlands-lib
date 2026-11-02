# Binary normalized product exactness

Author: Worker 321.

`Langlands.Aubert.binaryProductExactness` proves exactly the published
`Langlands.Aubert.BinaryProductExactnessStatement.{uF,uV} F T`. It quantifies
an arbitrary prime `p`, `F : PadicField.{uF} p`, and the supplied
`T : F.TopologicalData`, with independent carrier parameter `uV`.
The target's input and output representation carriers are in
`Type (max uF uV)`. The theorem adds no hypothesis.

For every pair of natural ranks `a,b`, the actual
`T.binaryNormalizedProductFunctor a b` preserves the supplied finite-length
short exact sequences separately in each variable, with every supplied
finite-length object fixed in the other variable. The conclusion is precisely
the conjunction of `SmoothRep.PreservesFiniteLengthShortExactLeft` and
`SmoothRep.PreservesFiniteLengthShortExactRight`. It concerns the functor's
actual images of the supplied maps, proving injectivity, surjectivity, and
equality of linear range and kernel in the order prescribed by
`SmoothRep.IsShortExact`.

## Linear exactness and carrier transport

`BinaryProductExactness.rTensor_exact` and `lTensor_exact` establish the three
conditions for ordinary complex tensor products. Every complex vector space is
flat, so Mathlib's
`Module.Flat.rTensor_preserves_injective_linearMap` and its left counterpart
give injectivity. `LinearMap.rTensor_surjective` and its left counterpart give
surjectivity. Mathlib's root-level `rTensor_exact` and `lTensor_exact` give the
middle exactness from the original equality of range and kernel and the
surjectivity of the final map. Their kernel-range equality is reversed to match
the target. No splitting of the representation sequence is required.

`exact_of_equiv` transports these three conditions through three supplied
linear equivalences commuting with both maps. It proves injectivity by applying
the first equivalence and the original injection, and surjectivity by lifting
through the final equivalence and pulling the preimage back through the middle
equivalence. For the middle equality it transports membership in the kernel
and range element by element in both directions.

`tensorModel_exact` applies this transport to a bifunctor whose carrier is
naturally equivalent to the full binary tensor of its input carriers. The
naturality equation is required for every actual morphism pair. Specializing
it to `(f,id)` gives the usual right tensor map and specializing it to
`(id,f)` gives the usual left tensor map. Thus it checks both actual mapped
arrows, rather than identifying only their source and target objects.
The finite-length witnesses are never used to derive linear exactness.
In particular the argument covers nonsplit sequences in the smooth
representation categories.

## Positive ranks

For `a,b > 0`, the published binary product first forms the pair family,
then its finite external tensor product, then applies actual normalized
parabolic induction on `BlockShape.binary a b ha hb`.

`pairSplit` identifies the literal indexed tensor on `Fin 2` with the
ordinary tensor of its zero and one factors. It composes the published
`FiniteTensor.headTailLinearEquiv` with the singleton-tail equivalence
`PiTensorProduct.subsingletonEquiv`. `pairSplit_tprod` checks its value on
pure tensors. `pairSplit_map` checks the commuting equality for every indexed
family of linear maps, using the universal property of the indexed tensor and
the pure-tensor formula for `PiTensorProduct.map`.

In `positive_exact`, let `Φ` be the actual pair-family functor followed by
`FiniteTensor.externalFunctor`. The zero and one components of the actual
pair-family map are definitionally the two original morphisms, and the
underlying external map is `PiTensorProduct.map`. Consequently
`pairSplit_map` is precisely the naturality equation needed by
`tensorModel_exact`. This proves injectivity, surjectivity, and the middle
equality for both arrows of the actual smooth product-Levi tensor sequence.

The proof applies the published
`Langlands.Parabolic.normalizedInductionExactness` to these three actual
smooth tensor objects, their representations, their actual intertwiners,
and their stored smoothness proofs. Its three conclusions are reordered to
match `IsShortExact`. The resulting induced maps are definitionally the
images under `T.binaryPositiveProductFunctor`. The final theorem rewrites
the all-ranks functor using `binaryNormalizedProductFunctor_of_pos`, so the
maps in its conclusion are those of the requested functor.

## Zero ranks

When `a = 0`, the proof uses the published
`T.binaryLeftZeroTensorEquiv ha X` and its naturality theorem. When `a ≠ 0`
and `b = 0`, it uses `T.binaryRightZeroTensorEquiv hb X` and its naturality
theorem. Each equivalence identifies the actual functor carrier with the
full tensor `X.1 ⊗[ℂ] X.2`. The equivalences already incorporate the
published functor identifications, the carrier `ULift`, and the rank casts.
Their naturality equations identify the actual functor maps with
`TensorProduct.map` of the two input maps. `tensorModel_exact` therefore
proves both required directions in each boundary case.

The first branch includes `(a,b) = (0,0)`. Every supplied GL₀ representation
retains its complete vector-space carrier; none is replaced by the trivial
line or supplied with a chosen vector. The proof requires neither a
positive-rank hypothesis nor a finite-dimensionality argument.

## Provenance and proof dependencies

This is an internal consequence of the already published actual binary-product
construction, elementary complex tensor exactness, and the already proved actual
normalized-induction exactness. It does not introduce a new external
representation-theoretic assertion or require a proof from the original
literature beyond those published inputs.

The direct project imports are
`Langlands.Representation.Aubert.GradedGrothendieck`,
`Langlands.Representation.Parabolic.InductionExactnessProof`, and
`Langlands.Representation.Tensor.FiniteEquivalences`; the direct Mathlib imports
are `Mathlib.RingTheory.Flat.Basic` and
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`.
The proof changes none of those files or the Lean/Markdown pairs in the target's
import closure.

The mathematical inputs are the tensor and transport results described above,
the binary functor's positive-branch equality and zero-rank natural
equivalences, and `normalizedInductionExactness`. The latter's published
argument proves pointwise injectivity and middle exactness and uses smooth
induction surjectivity for the actual p-adic parabolic; its positive-half
character twist leaves the underlying linear maps unchanged. Thus the proof
retains the supplied topology, upper parabolic, positive-half normalization
and right translation of the original binary product.

The target module transitively imports classification-dependent finite-length
infrastructure. This proof does not use
`binaryProduct_preservesFiniteLength` or any classification or finite-length
preservation theorem as a mathematical input. That distinction is not a
classification-independence claim about the target's entire import closure.
Finite-length preservation, graded ring laws, general-field extensions, and
product-Levi Grothendieck comparisons remain separate results or obligations;
this file proves the exact short-exactness target.
