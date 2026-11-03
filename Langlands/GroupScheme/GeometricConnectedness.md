# Geometric connectedness of connected group schemes

This internal bridge expresses the actual group law of `Langlands.GroupScheme`
in the published `GoodReductionJacobian.RelativeGroupLaw` interface. It then
deduces geometric connectedness, and connectedness after every field extension,
for a connected group scheme whose structure morphism is locally of finite type
and quasi-compact. All schemes and fields have arbitrary universe `u`.

`relativeGroupLaw` transports multiplication, the identity and inversion through
`NeronModelInfra.schemeHomOverEquivOverHom`. Its group identities are those of
the actual group of points. Naturality of multiplication is preservation of the
pointwise multiplication by precomposition.

`geometricallyConnected_of_connected` applies the published identity-component
theorem
`GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent`.
That theorem supplies a geometrically connected open identity component.
Connectedness of the original scheme makes its underlying range the whole
scheme, so its open immersion is an isomorphism. Geometric connectedness
therefore transports to the original structure morphism.

`connectedSpace_baseChange_of_connected` applies the definition of geometric
connectedness to the specified field-valued point of the base. The resulting
pullback scheme is the actual base-changed group scheme. The smooth affine specialization supplies
local finite type and quasi-compactness through the existing morphism-property
instances. `IsConnectedReductive.connectedSpace_toAlgebraicClosure` applies this
specialization to the smoothness, affineness and connectedness already present
in `IsConnectedReductive`; it does not change that definition.

This is derived content from the published actual group-scheme and relative
group-law constructions, the published identity-component theorem, and Mathlib
pullback and open-immersion results. The imported identity-component theorem
retains its original Anthropic FLT attribution and source provenance in its own
paired Markdown. No new literature assertion is used here. This helper does
not prove dynamic-centralizer reductivity or the full Levi split-component
statement.
