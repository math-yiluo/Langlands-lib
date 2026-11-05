# Canonical completed-tensor decomposition at actual function-field places

For an actual global function field `K` over finite constants `k`, any finite
extension `L/K`, and every original curve place `p` of `K`, this unit constructs

`curvePlaceCompletion p ⊗[K] L ≃ₐ[curvePlaceCompletion p]`
`  (∀ q : CurvePlacesAbove k L p, curvePlaceCompletion q.1)`.

The factors are the actual adic completions at **all** original upper places.
The equivalence is induced by the original completion embeddings. Neither a
tensor decomposition nor local-degree equalities are supplied as hypotheses.

## Source and hypotheses

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, Example 4.2, printed p.10, uses this global-field completed-tensor
decomposition to reduce the local Weil comparison to finite extensions of
complete fields. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This is the function-field arithmetic construction underlying that passage.
The proof below is derived from the existing integral-closure and completion
constructions rather than a transcription of a separate proof in Conrad.

The fields `k`, `K` and `L` lie in one arbitrary universe. The hypotheses are
finite `k`, the three algebra structures, `FiniteDimensional K L`,
`IsScalarTower k K L`, an original `Algebra (RatFunc k) K` presentation with
`IsScalarTower k (RatFunc k) K`, and `FunctionField k K`. There is no separability
hypothesis on `L/K` or on the original rational-function presentation. There
is no supplied finite upper-place selection, finite-normalization premise,
prime/place equivalence, degree lower bound, or tensor injectivity premise.
The imported construction proves finiteness of the full upper-place subtype.

## Proof and declarations

All declarations lie in `Langlands.Global.CurvePlaceCompletedTensorEquiv`.
`allLocalDegree_sum` proves that the sum of completed local field degrees over
the entire `CurvePlacesAbove k L p` index equals `Module.finrank K L`.
The existing simultaneous tensor surjection bounds this sum from above.
For the reverse inequality, the actual prime/place correspondence gives the
fundamental identity `sum e(q) * f(q) = [L:K]`, while the proved local
completed-integer comparison bounds each product by its actual local degree.
Summing the pointwise bounds proves equality.

`localDegree_eq p q` proves the corresponding equality at each original upper
place: its completed local field degree is its original ramification index
times its original residue degree. The pointwise bounds and equality of the
two finite sums force equality term by term. Thus the construction also rules
out a defect term in this arithmetic setting; it does not assume that fact.

`allTensorMap_bijective` proves bijectivity of the original canonical map
`CurvePlaceCompletedProduct.allTensorMap`. Its source has dimension `[L:K]`
over the lower completion by base change. Its target has this same dimension
by the just-proved local-degree sum. The existing surjection between these
finite-dimensional modules is therefore bijective. The implemented proof
uses Mathlib's `OrzechProperty.bijective_of_surjective_of_finrank_le` and
explicit vector-space freeness witnesses to keep instance search bounded.

`allTensorEquiv p` is `AlgEquiv.ofBijective` of that same map. Its pure-tensor
law `allTensorEquiv_tmul` is literal: the `q` component of `a tensor x` is
`completionMap p q a * algebraMap L (curvePlaceCompletion q.1) x`.
`allTensorEquiv_one_tmul` specializes this to the original upper-field image
of `x`. These laws fix the original factor embeddings, which the subsequent
Weil point comparison needs.

## Reuse and remaining obligations

The implementation reuses `CurvePlaceCompletedProduct` for the canonical map,
weak-approximation surjectivity, full upper-place finiteness and degree upper
bound; `CurvePlaceCompletedIntegersExtension` for the proved local lower
bounds; and `CurvePlaceIntegralPrimes` for the original all-place fundamental
identity. Their actual integral-closure proof handles finite extensions over
finite constants without replacing the given rational presentation by an
assumed separable one.

This unit constructs an algebra equivalence of these original rings. The Weil
scheme point homeomorphism, integral-model comparison and global adelic
homeomorphism remain separate construction and proof obligations.
