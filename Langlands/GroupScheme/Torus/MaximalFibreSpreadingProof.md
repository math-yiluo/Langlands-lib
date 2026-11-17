# Spreading maximality from a fibre with reductive identity component

Worker 855, with Worker 5600 (the separate fibre base-change helper).

## Result and source

`Langlands.GroupScheme.maximalTorusFibreSpreading` proves exactly
`Langlands.GroupScheme.MaximalTorusFibreSpreadingStatement.{u}` for every universe
`u`. The statement is imported unchanged from
[`MaximalFibreSpreadingStatement`](MaximalFibreSpreadingStatement.md).

Let `G` be a smooth relatively affine group scheme over any scheme `S`, and let
`i : T.toGrp ⟶ G` be a closed relative torus. Suppose the identity component of
the geometric fibre at `s` is connected reductive and the residue-fibre torus
`i_s` is maximal. The theorem produces an open `V` containing `s` such that:

- the residue-fibre map `i_v` is a maximal torus for every original point
  `v : S` belonging to `V`;
- for every representative `z : Z ⟶ G` of the all-test centralizer of `i`, and
  every `j : T.toGrp ⟶ Z` with `j ≫ z = i`, the map `j_V` represents the relative
  identity component of `Z_V`.

No additional hypotheses on `S`, the fibres of `G` away from `s`, or the chosen
representative `Z` are imposed.

The target is Conrad, *Reductive group schemes* (2014), Proposition 3.1.9(2),
printed pages 85–86; source ID `conrad-2014-reductive-group-schemes`, PDF
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Conrad first uses the smooth closed centralizer and then a local dimension
comparison and the fibral isomorphism criterion. The implementation retains the
centralizer and relative identity-component argument and replaces that dimension
comparison with the published smooth group monomorphism isomorphism-spreading
theorem. The auxiliary results below are internal consequences of existing
Library results, introduced for this proof.

## Implemented proof

Choose a smooth closed representative `c : C ⟶ G` of `Z_G(T)`, using
`relativeTorusCentralizer_hasSmoothClosedRepresentative`, and a smooth
geometrically connected relative identity component `e : H ⟶ C`, using
`RelativeIdentityComponent.smoothStructure`. Commutativity gives the canonical
closed factor `a : T.toGrp ⟶ C`. Geometric connectedness of the relative torus
lifts `a` through `e`, yielding `f : T.toGrp ⟶ H` with `f ≫ e = a` and
`f ≫ e ≫ c = i`.

On the geometric fibre at `s`, residue-fibre maximality becomes maximality after
extension to the algebraic closure, by
`isMaximalTorus_fieldPoint_of_residueFibre`. Both `T` and `H` on this fibre factor
through the identity component of `G`. That identity component is connected
reductive by the hypothesis at `s`, and its maximal torus is self-centralizing
by `maximalTorusCentralizer`. The image of `H` centralizes the torus, so it is
contained in that torus. The existing comparison from the torus to `H` therefore
has an inverse, as checked by cancellation of the subgroup monomorphisms.
Consequently the geometric-fibre map `f` is an isomorphism.

[`MaximalFibreSpreadingBaseChange`](MaximalFibreSpreadingBaseChange.md), supplied
by Worker 5600, reflects this isomorphism to the original residue field using
fpqc descent along its algebraic closure. The underlying map of `f` is a
monomorphism since its composite with `e ≫ c` is the closed immersion `i`.
Both its source and target are smooth over `S`, and the target has geometrically
connected fibres. Thus `SmoothMonoLocalIso.isIsoNear_of_residueFiber` supplies an
open `V` around `s` on which the underlying map of `f` is an isomorphism. The
forgetful functor reflects it to an isomorphism of group schemes.

On `V`, the inclusion `a` is the composite of this isomorphism with the open
inclusion `e`, so it is open; it is also closed. Its source has geometrically
connected fibres. The helper `component_of_open_closed` therefore identifies it
with the relative identity component of `C_V`.

For the first conclusion, the proof lifts each original residue-field point
`Spec κ(v) ⟶ S`, for `v ∈ V`, through `V`. Naturality of the pullback-composition
isomorphisms transfers the isomorphism of `f_V` to the original residue-fibre
map `f_v`. Thus `a_v` is again open and closed with geometrically connected
source, and represents the identity component of `C_v`. The helper
`isMaximalTorus_of_component` then proves maximality of `i_v`: any containing
torus centralizes `T_v`, factors through `C_v`, and by geometric connectedness
factors through its identity component `T_v`. The resulting reverse map is an
inverse to the given containment by cancellation of the closed inclusions.
This step needs no reductivity assumption at `v`.

For the second conclusion, any supplied representative `z : Z ⟶ G` is
canonically isomorphic to `C` over `G`. Uniqueness of factorization through the
monomorphism `z` identifies the supplied `j` with `a` followed by that
isomorphism. After restriction to `V`, its underlying map is open and closed,
and its source is geometrically connected. A final application of
`component_of_open_closed` gives the required all-test relative
identity-component property for this particular `Z`, `z`, and `j`.

## Auxiliary declarations

The namespace `Langlands.GroupScheme.MaximalFibreSpreading` contains:

- `liftToComponent` and `liftToComponent_comp`: a homomorphism from a
  geometrically connected group factors through a represented relative identity
  component. The construction uses the all-test identity-component condition
  and the open-immersion lifting property.
- `isIso_of_connected_centralizing`: over a field, in a smooth relatively affine
  group with connected reductive identity component, a connected monic subgroup
  that centralizes a maximal torus and contains it via a supplied map is
  isomorphic to that torus via the supplied map. No smoothness or affineness of
  this subgroup is required. The proof uses the identity component and
  `maximalTorusCentralizer` as above.
- `component_of_open_closed`: an open and closed group inclusion with
  geometrically connected source represents the relative identity component.
  In each residue fibre, its connected image is open and closed and contains
  the identity, hence equals the identity component; the residue-fibre
  characterization supplies the all-test property.
- `isMaximalTorus_of_component`: over any field, a closed torus that represents
  the relative identity component of a representative of its centralizer is
  maximal. The proof is the competing-torus factorization argument above.
- `isIso_of_underlying`: a group-scheme homomorphism whose underlying scheme map
  is an isomorphism is an isomorphism of group schemes. It uses reflection by
  `Over.forget` and `Grp.mkIso'`.
- `isIso_geometric_comparison`: packages the initial geometric-fibre argument
  for a supplied centralizer, identity component and comparison.
- `isIso_baseChange_comp`: naturality of `baseChangeCompIso` transfers an
  isomorphism of iterated pullbacks to the pullback along the composite.
- `isIso_residueFibre_of_restriction`: an isomorphism after restriction to an
  open gives an isomorphism on every original residue fibre at a point of that
  open, using an explicit lift of the residue-field point.
