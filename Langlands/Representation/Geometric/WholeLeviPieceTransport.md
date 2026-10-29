# Whole-target geometric pieces in flattened coordinates

Author: Worker 514.

This is an internal algebraic construction from the published concrete
flattened-Levi equivalence, geometric piece functor, and transport and
full-refinement induction equivalences. It asserts no new literature theorem.
It supplies a prerequisite for identifying actual geometric grades, not a proof
of the supported multiplicity obstruction.

For a block shape `B`, a refinement `S`, and another block shape `C` of the same
rank, suppose the permutation `w` conjugates the embedded Levi of `B.flatten S`
onto the embedded Levi of `C`. The theorem
`sourceLevi_eq_refined_of_flattened_conjugates` identifies the source
intersection with `refinedLevi F B S`. The theorem
`targetLevi_eq_top_of_flattened_conjugates` identifies the target intersection
with the whole target Levi. Neither assertion requires minimality of `w`.

The auxiliary membership equivalence follows from both ambient embedding
identities for `flattenedLeviEquiv` and injectivity of the coarse Levi embedding.
Conjugation is injective, so membership in its subgroup image reduces to this
membership equivalence. The target fullness follows from the published
whole-Levi conjugation identity and the inclusion of the flattened Levi in the
coarse Levi, also proved using the same embedding identity.

For a p-adic field with compatible topological data `T`,
`wholeLeviGeometricPieceEquiv` constructs an actual representation equivalence
from the geometric piece on an arbitrary smooth representation `A` of `B.Levi`
to

```lean
CuspidalSupport.transport (B.flatten S) C w hw
  ((T.normalizedRefinedJacquet B S A.representation).comp
    (flattenedLeviEquiv F.Carrier B S).toMonoidHom)
```

Its parameters include the actual source and target subgroup equalities used
by `geometricPieceFunctor`. They may be any such equalities; the source one is
also established in this module. The target refinement is arbitrary subject
to its equality, hence its Levi is full by the preceding target identity.

The proof retains the source normalized refined Jacquet module. Pulling it
back to flattened coordinates and then back along the inverse coordinate map
is intertwined with the original module by the identity linear map. The
published `subgroupEqualityCompEquiv` and `intersectionTransportEquivOf` in
`Classification.SegmentEdgeJacquetReduction` then compare the middle transport
with the restriction of the displayed whole-Levi transport. The published
`subgroupEqualityEquiv` relabels the target subgroup. Finally,
`fullRefinedInductionEquiv` evaluates induction from the full target at the
identity, with the full-refinement modulus and projection identities proved in
its original module. Smoothness follows by continuous pullback along
`flattenedLeviEquivContinuous` and the published smoothness of Weyl transport.

The field universe and the representation carrier universe are independent.
No positivity of the ambient rank, source cuspidality, minimality, branch
certificate, multiplicity comparison, or continuation premise is added.
The new result is an equivalence of the upper geometric piece; it does not
itself compare opposite grades or produce a selected Weyl branch.
