# Exact finite unramified recovery containing prescribed coefficients

This internal construction strengthens `finiteUnramifiedRecovery` by retaining
a prescribed finite subfield in the recovered model's coefficient field. Its
provenance is the existing actual-field `fieldFactorization`, the spectral
group-model construction, integral pullback comparisons and exact generic
isomorphism recovery. It asserts no original-literature theorem.

Let `F` be a nonarchimedean local field with the Library's compatible valuation
and topology. All fields and schemes have a common arbitrary universe.

`exists_common_finiteUnramified` takes two finite intermediate fields of the
chosen separable closure, each contained in the inertia fixed field. Their
compositum is finite and remains in the inertia fixed field. Apply
`fieldFactorization` to its actual inclusion into that fixed field. The
factorization identity proves that the resulting finite Galois arithmetically
unramified field contains both original fields as actual subfields of the
separable closure.

`SpectralGroupModel.enlarge` takes a spectral model and a containing finite
Galois arithmetically unramified field within the inertia fixed field. It pulls
the model back along the actual integer-ring inclusion. Affineness and
smoothness follow by base change. Its integral recovery is the original
recovery isomorphism followed by the inverse of `stageIntegralComparison`.
This construction does not yet prescribe a generic-fibre identification.

`finiteUnramifiedRecovery_above` takes a group scheme `G/F`, a supplied smooth
integral model `P` of its base change to the inertia fixed field, and a supplied
finite intermediate field `E₀` contained in that fixed field. It first chooses
a spectral group model of `P.group`, then a common field containing its field
and `E₀`, and enlarges the spectral model to that common field.

The existing `nonempty_modelIsoStage` further enlarges this model's field so
that the prescribed generic identification of `P` is recovered exactly.
`finiteRecoveryAt_of_rawStage` then gives `HasFiniteRecoveryAt` over this final
field. The conclusion retains its finite degree, Galois property, arithmetic
unramifiedness, containment in the inertia fixed field, and containment of
`E₀`. The model recovery uses precisely `finiteInertiaGenericIso`, as required
by `HasFiniteRecoveryAt`.

The theorem assumes the existence and smoothness of `P`; it does not construct
a point-stabilizer model, a cocycle or an integral descent datum, and it has no
residue, Frobenius, quotient or chamber conclusion.
