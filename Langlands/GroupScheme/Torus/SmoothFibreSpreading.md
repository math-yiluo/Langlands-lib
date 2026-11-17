# Spreading a torus fibre in a smooth affine group

Worker 606.

This is an internal derived helper for the proof of
[`TorusFibreSpreadingStatement`](FibreSpreadingStatement.md). It proves the smooth
case in every universe, assuming geometric connectedness of the structure
morphism. It also proves a lemma converting connected residue fibres of a
locally finite-type affine group into geometric connectedness. The original
statement pair and its imports are unchanged.

## Declarations and hypotheses

- `Langlands.GroupScheme.geometricallyConnected_of_connected_residueFibres`
  takes an arbitrary base scheme and a group whose structure morphism is locally
  of finite type and affine. If every actual residue-field fibre is connected,
  the structure morphism is geometrically connected. No smoothness or flatness
  is assumed in this lemma.
- `exists_etale_split_of_split_residueFibre` takes a smooth affine group with
  geometrically connected fibres and a split torus residue fibre at `s`. It
  produces an étale morphism `q : V → S` whose image contains `s` and for which
  the actual group pulled back along `q` is split.
- `exists_etale_split_of_torus_residueFibre` has the same conclusion with the
  field predicate `IsTorus` in place of `IsSplitTorus`.
- `relativeTorus_etaleImage_of_split` takes any group and any étale map which
  splits its pullback. Its open image is a base over which the group is a
  relative torus. The map need not be surjective onto the original base.
- `exists_open_torus_of_smooth_torus_residueFibre` combines the last two
  constructions. Its conclusion is an open `U` containing `s` for which the
  actual restricted group satisfies `RelativeTorus.IsTorus`.

All the group schemes, schemes, and field extensions are in universe `u`. A
relative torus here means an étale form of split tori with finite rank; the rank
need not be constant on the base.

## Implemented proof

For the geometric-connectedness lemma, Mathlib's fibrewise criterion reduces
the assertion to residue fibres. Such fibres are finite-type groups over fields
because the structure morphism is locally of finite type and affine. The
published `geometricallyConnected_of_connected` then applies to each fibre.

For a split residue fibre, the proof applies `relativeSplitTorusLifting` to the
identity inclusion of the whole fibre. The exact recovery equation makes the
lifted inclusion an isomorphism on the specified field-valued fibre.
`isIso_residueFibre_of_fieldPoint` reflects this isomorphism to the canonical
residue fibre at the image of that point. A split torus is smooth, and the
lifted inclusion is a closed immersion and hence a monomorphism. Thus
`SmoothMonoLocalIso.isIsoNear_of_residueFiber` gives an open neighbourhood
upstairs on which the inclusion is an isomorphism. The resulting group over
that neighbourhood is split. Composing its open immersion with the original
étale neighbourhood gives the required étale map.

For an arbitrary torus fibre, `torusFiniteGaloisSplitting` supplies a finite
Galois splitting field. `etaleResidueExtension` realizes that field as the
residue field of an étale neighbourhood, with the prescribed scalar structure.
`EtaleResidueExtensionData.groupFibreIso` and the actual base-change composition
isomorphism identify its new residue fibre with the split field extension.
The split case applies upstairs, and composition of the two étale maps gives
the asserted splitting neighbourhood.

Finally, the splitting map factors through its open image. The factor is
étale and surjective. The actual composition isomorphism transports splitness
to the iterated pullback, and
`RelativeTorus.IsTorus.of_baseChange_of_etale` descends the relative-torus
property to that open image.

## Provenance

This is a derived implementation of the smooth part of Conrad's Corollary
3.1.8, using the already published split-torus lifting theorem and the smooth
monomorphism local-isomorphism theorem. It replaces the dimension argument in
Conrad's proof by the latter theorem. It does not yet reduce an arbitrary fppf
group to a smooth neighbourhood.

Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`,
Corollary 3.1.8, pp.84–85 (smooth case on p.85).
