# Spreading self-centralization using a supplied closed centralizer

Author: Worker 606.

`Langlands.GroupScheme.selfCentralizingTorusOpen.{u}` constructs an open
neighbourhood where an actual closed relative torus is self-centralizing and
maximal on every residue fibre. The base `S : Scheme.{u}` is arbitrary. The
ambient group `G/S` is locally of finite type and has connected reductive
actual residue fibres, expressed by `HasConnectedReductiveResidueFibers G`.
The input includes an actual closed inclusion `t : T.toGrp ⟶ G` for a
commutative group scheme whose underlying group is a relative torus. It also
includes an actual closed homomorphism `c : C ⟶ G` representing the whole
all-test centralizer `torusCentralizer t`. Finally, `t` is required to be a
maximal torus in the specified residue fibre at `s : S`.

There is no global smoothness, affineness, separation or quasi-compactness
assumption on `G/S`, and no smoothness assumption on `C/S`. The closed
centralizer representative is supplied. The separate
`separatedRelativeTorusCentralizerModel` construction supplies one whenever
the ambient group is separated; this module does not import that construction.

The output `SelfCentralizingTorusOpenData t c s` consists of an actual open
`V` containing `s`, an actual group-scheme isomorphism `T_V ≅ C_V` whose
forward map followed by `c_V` equals `t_V`, the equality
`torusCentralizer t_V = SubgroupFunctor.range t_V`, and
`IsFibrewiseMaximalTorus t_V`. The equality is between subgroup functors on
all schemes over `V`, including nonaffine and nonreduced tests. Fibrewise
maximality concerns the literal residue-field pullback at every point of `V`.
Affineness of `G` or of its restriction to `V` is not concluded.

## Implemented construction

The helper
`torusCentralizer_geometricallyConnected_of_residueReductive` proves that
`C/S` has geometrically connected fibres. For every actual field-valued point
`b : Spec k ⟶ S`, the published
`fieldReductive_of_residueReductive` makes `G_b` connected reductive, hence
smooth, connected and affine over that field. Base change of the supplied
representing homomorphism represents the centralizer of the base-changed
torus. Relative tori over fields are field tori by
`RelativeTorus.IsTorus.isTorus`. The published
`IsTorus.connectedSpace_centralizer` therefore makes `C_b` connected. The
all-field-points criterion gives geometric connectedness. This helper does
not require `C/S` smooth or closed, or `G/S` locally of finite type.

Let `f : T ⟶ C` be the canonical `torusCentralizerFactor t hc`, satisfying
`f ≫ c = t`. The helper `isIso_torusCentralizerFactor_residueFiber` works at
a selected connected reductive residue fibre. By `maximalTorusCentralizer`,
`T_s` equals its full centralizer when it is maximal. The actual maps `t_s`
and `c_s` then represent the same subgroup functor. The represented-subgroup
isomorphism and its inclusion compatibility identify its forward map with
the literal base change `f_s`, so `f_s` is an isomorphism. This helper does
not require smoothness of the centralizer.

The relative torus `T/S` is smooth, in particular flat and locally of finite
presentation. The centralizer `C/S` is locally of finite type because `c` is
closed and `G/S` is locally of finite type. The factor `f` is closed because
`t` and `c` are closed. Apply the new
`FlatClosedLocalIso.isIsoNear_of_residueFiber` to `f` and the selected fibre.
Its proof is documented in `Langlands/GroupScheme/FlatClosedLocalIso.md`.
It requires only a flat locally finitely presented source, a locally
finite-type target with geometrically connected fibres, and closedness of
the inclusion. Thus no centralizer-smoothness theorem is used. It yields an
open `V` containing `s` on which `f` is an isomorphism of underlying schemes.
The forgetful functors reflect isomorphisms, giving the actual group-scheme
isomorphism `T_V ≅ C_V` and its inclusion equation.

Base change of the representing property identifies the full centralizer of
`t_V` with the range of `c_V`. The comparison isomorphism and
`SubgroupFunctor.range_iso_comp` identify that range with the range of `t_V`.
The equality commutes with arbitrary base change, by
`torusCentralizer_baseChange` and `SubgroupFunctor.range_baseChangeHom`.
Each residue-fibre torus is therefore self-centralizing and hence maximal
by `isMaximalTorus_of_torusCentralizer_eq`. These constructions prove
`nonempty_selfCentralizingTorusOpenData`; the exported constructor uses
classical choice to select the actual data.

## Internal provenance and consumer obligations

This is an internal composition of published residue-to-field reductivity,
connectedness of field torus centralizers, field maximal-torus
self-centralization, represented-subgroup comparisons, and the accompanying
extension of the local-isomorphism method for closed group inclusions. No new
external theorem is assumed. Its intended consumer is
`ReductiveFiberAffinenessStatement`. A lifted relative torus and a closed
centralizer remain inputs here, while the torus-moduli and Weyl-affineness
proofs needed by the exact target remain separate obligations.
