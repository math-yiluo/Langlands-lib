# Étale transport of relative Borel subgroups

This supporting module supplies transport for the descent step in Conrad,
*Reductive group schemes* (2014), Proposition 5.2.12, p.158. The relative
Borel predicate is the one from Definition 5.2.10, p.157. These are derived
applications of the existing Library definitions and transport theorems;
the source motivates their role and is not claimed to contain these exact
categorical interfaces.

`IsRelativeBorelSubgroup.baseChange_of_etale` says that, for group schemes
over an arbitrary scheme and an affine ambient group, the actual pullback
of a relative Borel inclusion along an étale map is a relative Borel
inclusion. Neither reductivity nor closedness of the original inclusion is
an extra premise. Smoothness and relative affineness of the source and
monicity of the inclusion pull back. The geometric Borel property on each
residue fibre supplies its parabolic property.

`IsRelativeBorelSubgroup.of_etale_cover` assumes a supplied closed inclusion
into an affine ambient group, and a jointly surjective étale cover indexed
in the scheme universe. If every actual pullback inclusion is relative
Borel, the original inclusion is relative Borel. The closedness premise is
explicit: this theorem does not construct the descended closed subgroup.
It yields global relative affineness and monicity. For each point of the
base, a point above it in the cover supplies geometric Borelness by
reflection along the induced algebraic extension of residue fields.

The geometric fibre arguments use the following supporting results.

- `IsGeometricBorelSubgroup.baseChange_of_algebraicExtension` assumes an
  affine ambient field group and an algebraic extension. It transports the
  Borel over the chosen algebraic closure through the actual comparison
  isomorphism of successive base changes. The map between the chosen
  algebraic closures is an isomorphism because the extension is algebraic.
  Published algebraic-closure reflection then supplies the full geometric
  Borel predicate over the extension.
- `RelativeLevi.isGeometricBorelSubgroup_iterated_baseChange_iff` transports
  geometric Borelness through the explicit natural pullback comparison.
  `RelativeLevi.isGeometricBorelSubgroup_residueFiber_baseChange_iff` applies
  it to the natural residue-field square.
- `IsGeometricBorelSubgroup.residueFiber_baseChange_of_etale` and
  `IsGeometricBorelSubgroup.of_residueFiber_baseChange_of_etale` apply the
  algebraic-extension ascent and the published reflection theorem to that
  square. Étaleness makes the residue-field extension separable and hence
  algebraic. Reflection retains the closedness premise for the original
  fibre inclusion.

`RelativeLevi.smooth_of_etale_cover_pullbacks` proves the smoothness step in
cover reflection. Pull the cover back to the source, take the coproduct of
its components, and use that the projection to the source is étale and
surjective. Each component's map to the original base is smooth by
composition. Smoothness on a coproduct is local on its source, so the
coproduct composite is smooth. The published
`smooth_of_smooth_of_surjective_of_smooth_comp` then descends smoothness.
The cover index is in the scheme universe, so its coproduct exists there;
no compactness or finite-type assumption on the base is used.

`IsRelativeBorelSubgroup.iso_comp` and
`IsRelativeBorelSubgroup.comp_iso` transport the full relative predicate
through isomorphic source and ambient presentations. For source transport,
the structural morphism factors through the source isomorphism. In each
case, the residue-fibre inclusion is the corresponding composition after
base change, so the existing geometric Borel transport lemmas apply.

This module proves transport and reflection only. It does not construct
opposite Borels, prove their uniqueness, or eliminate the local dynamic
presentation and Lie-containment prerequisites of the opposite Borel proof.

The declarations `IsRelativeBorelSubgroup.iso_comp` and `IsRelativeBorelSubgroup.comp_iso` described above are imported from `Langlands.GroupScheme.RelativeLevi.BorelTransport`.
