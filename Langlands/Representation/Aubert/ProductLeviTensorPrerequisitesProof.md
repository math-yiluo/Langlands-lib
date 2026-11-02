# Finite length and exactness for the actual positive product-Levi tensor

Author: Worker 158. Scope and dependency checks: Worker 1004.

`Langlands.Aubert.productLeviTensorPrerequisites` proves the published
`ProductLeviTensorPrerequisitesStatement.{uF,uV} F T ha hb`. Its parameters
are a prime `p`, the actual `F : PadicField.{uF} p`, its supplied topological
data `T`, and two positive natural ranks. The field and representation
universes are independent; the smooth complex representations have carriers
in `Type (max uF uV)`. The conclusion is the conjunction of the three
published preservation predicates for `binaryProductLeviTensorFunctor`.

For finite length, form the actual binary family using
`T.binaryPairFamilyFunctor ha hb`. Its two coordinates have finite
group-algebra length by the supplied assumptions. The published
`glFiniteLengthAdmissibility` gives their admissibility.
`Classification.ProductLengthProof.selfMatching_of_finiteLength` converts
each finite composition series to self-matching Jordan–Hölder factors.
Apply the published `FiniteTensor.padicExternalTensorFactors` to this
family paired with itself, and extract its actual external tensor
composition series. The published
`LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength`
gives finite length of the actual output representation. This argument
includes reducible and zero factors.

For exactness, `binaryEquiv` composes the published
`FiniteTensor.headTailLinearEquiv` with the singleton indexed-tensor
equivalence. It identifies the actual indexed carrier with the ordinary
two-factor complex tensor carrier. Its formula on pure tensors sends
the indexed pure tensor of `v` to `v 0 ⊗ v 1`.
`binaryEquiv_map` proves naturality for arbitrary coordinatewise linear
maps by pure-tensor spanning and linearity. After specializing to the
actual binary family functor, `carrierEquiv_naturality` compares its actual
mapped morphisms with `TensorProduct.map` of the two supplied
intertwiners. It covers both arrows of each sequence and either position
of the identity morphism.

For a fixed second factor, the ordinary maps are `f.rTensor D` and
`g.rTensor D`. Complex vector spaces are flat, so Mathlib's
`Module.Flat.rTensor_preserves_injective_linearMap` gives injectivity.
`LinearMap.rTensor_surjective` gives surjectivity, and
`rTensor_exact` gives equality of range and kernel from the
original exactness and surjectivity. For a fixed first factor, the proof
uses the corresponding three `lTensor` results.
`shortExact_of_equiv` transports these three conditions through the
three actual carrier equivalences and the two naturality identities.
Consequently the conclusion concerns exactly the actual functor images
required by `SmoothRep.IsShortExact`, for all the supplied sequences,
including nonsplit sequences and arbitrary finite-length fixed factors.
No equivariant splitting of the input sequence is used.

This is an internal consequence of published tensor and representation
results, for the actual functor constructed in `ProductLeviGrothendieck`.
That construction records Aubert 1995, printed p.2184, and Zelevinsky 1980,
§1.7, printed pp.172–173; the product-Levi correction is explained in
`notes/henniart/aubert-duality-route.md`. The implemented proof is the
composition-series and actual-map argument above, rather than a direct
formalization of a source paragraph.

The finite-length proof retains the transitive dependencies of the
published finite-length admissibility and tensor factor-matching theorems.
In particular, importing the published self-matching helper from
`Classification.NormalizedProductFiniteLengthProof` retains that module's
existing classification and parabolic induction imports. These imports
are visible dependencies, even though the tensor exactness arguments
are linear algebra and the final theorem has no additional
representation-theoretic hypothesis. The target and its imported
Lean/Markdown pairs are preserved.
