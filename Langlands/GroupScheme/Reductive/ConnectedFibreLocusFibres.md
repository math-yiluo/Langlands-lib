# Connected fibres of smooth affine groups under field extension and base change

Field-level lemmas used in the proof of
`Langlands.GroupScheme.ConnectedFibreLocusClosedStatement` (Conrad, *Reductive group
schemes* (2014), Proposition 3.1.12). All declarations are in the namespace
`Langlands.GroupScheme.ConnectedFibreLocus`.

## `connectedFibreLocus`

For a group scheme `G` over a scheme `S`, the set of points `s ∈ S` whose residue-field
fibre `RelativeIdentityComponent.residueFiber G s` (the base change of `G` along
`Spec κ(s) → S`) has connected underlying space. This is exactly the set in the target
statement.

## `connectedSpace_of_iso`, `connectedSpace_iff_of_iso`

Connectedness of the underlying space of a group scheme is invariant under isomorphism of
group schemes over the same base. *Proof.* The underlying morphism of schemes of an
isomorphism is an isomorphism, hence a surjective continuous map, and continuous images of
connected spaces are connected.

## `geometricallyConnected_iff_connectedSpace`

A smooth affine group `H` over a field `k` is connected if and only if its structure
morphism is geometrically connected. *Proof.* Geometric connectedness gives connectedness
by the base change along the identity (Mathlib's
`GeometricallyConnected.connectedSpace_of_subsingleton`). Conversely, a connected smooth
affine group over a field is geometrically integral (the Library's
`smoothConnectedAffineGeometry`), hence geometrically irreducible, and irreducible spaces
are connected.

## `connectedSpace_baseChange_iff`

For a field homomorphism `φ : k → K` and a smooth affine `k`-group `H`, the base change
`H_K` is connected if and only if `H` is. *Proof.* The projection `H_K → H` is surjective
(base change of the surjection `Spec K → Spec k`), so connectedness descends. Conversely a
connected `H` is geometrically connected by the previous lemma, so `H_K` is connected.

## `smooth_baseChange`, `isAffineHom_baseChange` (instances)

Smoothness and affineness of the structure morphism of a group scheme are preserved by the
group-scheme base change `baseChange b` along any morphism `b : T ⟶ S`. *Proof.* The
structure morphism of the base change is the second projection of the pullback along `b`,
and both properties are stable under base change.

## `connectedFibreLocus_eq`

For a smooth affine group `G` over `S`, `connectedFibreLocus G` equals the Library's
geometrically connected fibre locus `geometricallyConnectedFiberLocus G.X.hom` (the points
whose residue-field fibre is geometrically connected). *Proof.* Pointwise, the
residue-field fibre is a smooth affine group over the field `κ(s)`, so
`geometricallyConnected_iff_connectedSpace` applies.

## `isLocallyConstructible_connectedFibreLocus`

The connected-fibre locus of a smooth affine group is locally constructible in `S`, over an
arbitrary base scheme. *Proof.* By `connectedFibreLocus_eq` and the Library's published
local constructibility of the geometrically connected fibre locus of a morphism
(`geometricallyConnectedFiberLocalConstructibility`), which applies to the structure
morphism since it is smooth, hence locally of finite presentation, and affine, hence
quasi-compact and quasi-separated.

## `connectedFibreLocus_baseChange`

For `b : T ⟶ S`, the connected-fibre locus of the base change `G_T` is the preimage under
`b` of the connected-fibre locus of `G`. *Proof.* By `connectedFibreLocus_eq` on both sides
and the Library's base-change compatibility of the geometrically connected fibre locus
(`geometricallyConnectedFiberLocus_baseChange`) for the pullback square defining `G_T`.

## `connectedSpace_iff_mem_connectedFibreLocus`

A smooth affine group `H` over a field `k` is connected if and only if the unique point of
`Spec k` lies in `connectedFibreLocus H`. *Proof.* By `geometricallyConnected_iff_connectedSpace`,
connectedness of `H` is geometric connectedness of its structure morphism, which is
equivalent to the geometrically connected fibre locus being all of `Spec k`
(`geometricallyConnectedFiberLocus_eq_univ_iff`); as `Spec k` has one point, this means the
closed point lies in the locus.

## `connectedSpace_fieldPoint_iff`

For a smooth affine group `G` over `S` and a field-valued point `b : Spec k ⟶ S`, the base
change `G_k` is connected if and only if the image `b(pt)` of the unique point lies in
`connectedFibreLocus G`. *Proof.* Combine `connectedSpace_iff_mem_connectedFibreLocus` for
`G_k` with `connectedFibreLocus_baseChange`. In particular connectedness of `G_k` depends
only on the image point and not on the field `k` (a form of
`connectedSpace_baseChange_iff`).
