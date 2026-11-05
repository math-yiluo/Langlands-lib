# Geometry of the open relative identity restriction

This derived helper discharges the geometric-connectedness input of
`RelativeIdentityComponent.exists_of_isOpen`. The ambient group scheme is
smooth over an arbitrary base scheme, and the relative identity set is assumed
open. No affineness or quasi-compactness assumption is imposed.

`identityFiberOver` is the actual pullback of the raw open restriction to a
residue field. `identityFiberInclusion` is the pullback of its open immersion
into the ambient scheme. These constructions precede any group law on the
restriction and therefore avoid assuming the subgroup being constructed.

The scheme pullback image formula, `range_inclusionOver`, and
`fiberι_mem_underlyingSet_iff` show that the fibre inclusion has image precisely
the ambient fibre's identity connected component. Its underlying map is an
embedding. The resulting homeomorphism with its range gives connectedness of
the source. `identityFiberOne` is the base change of `openOne`, with the lax
monoidal unit comparison supplying its domain.

Smoothness is preserved by this base change. The published smooth connected
pointed field-scheme theorem then gives geometric connectedness of every raw
residue fibre. The residue-fibre criterion for geometric connectedness gives
`identityOver_geometricallyConnected`.

The auxiliary consequences `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.isIntegral_of_smooth_of_connectedSpace` and
`irreducibleSpace_of_smooth_connected` use the published smooth domain-stalk
theorem and connected locally Noetherian integrality theorem. They need neither
a section nor affineness nor quasi-compactness. Their applications expose
integrality and irreducibility of the raw identity fibres.

Finally `smoothExistence_of_isOpen` applies the actual open-subgroup constructor,
now with its geometric-connectedness input proved. The remaining hypothesis is
openness of the relative identity set for every smooth group scheme. This helper
does not establish that openness or the unconditional aggregate task target.

The provenance is internal derivation from the named Library constructions,
range criteria, and geometric-connectedness results, together with Mathlib's
actual scheme pullbacks and open-immersion embeddings.

The integrality result is reused from the existing Anthropic FLT port;
the new raw-fibre constructions and irreducibility consequence retain their
reviewed hypotheses.
