# Exact generic recovery of finite unramified integral stages

This internal successor to `FiniteUnramifiedStage` proves exact generic
compatibility for its construction, expressed over two explicit intermediate
fields. It does not yet package that equality as a coefficient-base-change
`IntegralModel.Iso` or prove the final unramified model descent statement.

Let `F` be a nonarchimedean local field in an arbitrary universe `u`, and `N` an
integral model over the maximal-unramified integers of the scalar extension of a
group scheme `G/F`. Supply two intermediate fields `E ≤ E'` of the chosen
separable closure, both contained in the inertia fixed field, a group scheme
`H` over the actual spectral integers of `E`, and an isomorphism `d` identifying
`N.group` with the scalar extension of `H` to the maximal-unramified integers.
Supply an isomorphism `a` over `E'` from the extension of `G_E` to the extension
of the generic fibre of `H`. No finiteness, smoothness or Galois assumptions on
these fields or group schemes are needed for the comparison identities here.

`rawStageGenericIso` compares the generic fibre of the integral extension of
`H` to `E'` with `G_E'`. It composes `enlargementGenericSquare`, `a.symm`, and the
canonical comparison of the two base-field extensions.

`inertiaGenericSquare_enlargement` proves that taking the generic comparison
after integer enlargement equals first taking the finite generic comparison
and then the field-enlargement comparison. The proof reduces equality of the
isomorphisms to equality of their homomorphisms, then to equality of the
underlying projections all the way to `H`. The projection laws from
`FiniteUnramifiedStage` identify both sides. A private `comparison_tower` proves
the corresponding associativity law for three field pullbacks by the same
method, using only a single final pullback projection.

`rawStage_generic` assumes the exact recovery equation for `a`: pulling `a` to
the inertia fixed field with `pullIso` gives the comparison obtained from the
base-field pullback comparison, `N.genericIso.symm`, the generic pullback of `d`,
and `inertiaGenericSquare F E`. This is the equation carried by the earlier
`IsoStage` when its isomorphism is the supplied `stageGenericComparison`.

Its conclusion is an equality of actual group-scheme morphisms. On one side,
take the generic pullback of `stageIntegralComparison` followed by `d.symm`, then
`N.genericIso`. On the other side, first use `inertiaGenericSquare` at `E'`, then
the inertia pullback of the constructed generic isomorphism, and then the
canonical field comparison to `G` over the inertia fixed field. Thus the
integral-group recovery comparison respects the prescribed original generic
identification, in explicit square coordinates.

The implemented proof uses a private identity `recovery_square` valid in any
category. Inverting the supplied recovery identity and cancelling the middle
isomorphisms turns the two commuting-square identities into the desired
triangle identity. Applying that identity to the actual group-scheme
comparisons, and taking its forward morphism, yields `rawStage_generic`.

The provenance is internal. All inputs are actual isomorphisms and equalities;
no extension theorem, semilinear descent datum or effectiveness assertion is
assumed. The comparisons and their projection laws are imported by Lean name,
and their new coherence laws are proved from pullback extensionality and the
isomorphism identities.
