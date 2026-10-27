# Openness of connected components of a locally Noetherian scheme

`Langlands.AlgebraicGeometry.LocallyNoetherianConnectedComponentOpenStatement.{u}`
is the following `Prop`-valued definition:

```lean
∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]
  (x : X), IsOpen (connectedComponent x)
```

In words: for every scheme `X` in the arbitrary universe `u` that is locally
Noetherian, and every point `x` of `X`, the connected component of `x` in the
underlying topological space of `X` is an open subset of that space.

The statement uses Mathlib's own notions directly:

- `AlgebraicGeometry.Scheme.{u}` is an arbitrary scheme. There is no base
  scheme, base field, finiteness, quasi-compactness, separatedness or
  reducedness hypothesis. The scheme is used as given, including any nonreduced
  structure; nothing passes to the reduction or to another scheme with the same
  underlying space.
- `AlgebraicGeometry.IsLocallyNoetherian X` is Mathlib's local Noetherianity
  class: the ring of sections over every affine open of `X` is Noetherian. It
  is supplied as an instance argument. The underlying space of `X` is **not**
  assumed to be a Noetherian topological space; a locally Noetherian scheme can
  have infinitely many connected components or irreducible components.
- `connectedComponent x` is Mathlib's connected component of `x` in the
  underlying topological space of `X`, the union of all connected subsets
  containing `x`. `IsOpen` refers to the Zariski topology on that same space.
  The conclusion therefore concerns the actual underlying topological
  connected component, not an open subscheme constructed separately and not a
  component of some base change.

The statement does not assume `LocallyConnectedSpace X`. Mathlib's
`isOpen_connectedComponent` (in `Mathlib.Topology.Connected.LocallyConnected`)
gives openness of connected components from such an instance, but the pinned
Mathlib provides no local connectedness instance for locally Noetherian
schemes, so that theorem cannot be applied without first proving the needed
local topology. Establishing local connectedness is one possible proof route,
not an input. The proposition also does not itself assert local connectedness;
it asserts only the openness of every connected component.

This file defines the proposition; it does not prove it. A separate proof task
is to prove this exact published proposition.

## Derived provenance

This is an internal derived statement: a general topology prerequisite
extracted from the local-Noetherianity step of the identity-component argument
in the following original source.

B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary
version of the first chapters (book draft, PDF built 2012-02-08), literature ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, file
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`,
SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Paragraph (3.16), "The identity component of a group scheme over a field",
printed p.38 (PDF p.42), was read directly. Its second paragraph says:

> Assume in addition that G is locally of finite type over k. Then the scheme G
> is locally noetherian, hence locally connected. If we write G0 for the
> connected component of G containing e, it follows that G0 is an open
> subscheme of G.

No project errata note for this source was found.

The source makes this inference only for a group scheme `G` locally of finite
type over a field `k`, and only for the component `G0` of the identity point
`e`. It gives no separate proof of the step from local Noetherianity to local
connectedness or openness. The declaration isolates the purely topological
part of the inference and states it for every locally Noetherian scheme and
every point. This broader formulation is not a verbatim statement in the
source. It drops the group structure, the field and the finite-type
hypothesis, and keeps only local Noetherianity, which the source deduces from
local finite type over a field. The source's intermediate conclusion, local
connectedness, is not part of the declaration; only its consequence used in
(3.16), openness of the connected component, is stated.

The proposition supplies no Picard parameter, group law, identity point,
identity-component comparison, base-change compatibility or Picard-zero
conclusion. It is only the topology step. Applying it to a group scheme or a
Picard scheme requires separately establishing local Noetherianity of that
scheme and relating the relevant component to the objects of the later
argument.

## Mathematical justification of the statement

The following standard argument shows that the proposition is true. It is a
suggested route for the future formal proof, not an implemented Lean proof.

1. Let `T` be a Noetherian topological space and `C` a connected component of
   `T`. Every irreducible component of `T` is irreducible, hence connected, so
   an irreducible component meeting `C` is contained in `C`. The irreducible
   components cover `T`, so the complement of `C` is the union of the
   irreducible components disjoint from `C`. A Noetherian space has finitely
   many irreducible components, each closed, so this complement is closed and
   `C` is open in `T`.
2. Let `X` be locally Noetherian, `x` a point and `y` a point of the connected
   component of `x`. Choose an affine open `U` containing `y`. Its ring of
   sections is Noetherian, so the underlying space of `U` is a Noetherian
   topological space. By step 1, the connected component of `y` in `U` is
   open in `U`, hence open in `X`. It is connected and contains `y`, so it is
   contained in the connected component of `y` in `X`, which equals that of
   `x`. Thus the connected component of `x` contains an open neighbourhood of
   each of its points and is open.

The argument uses only one affine open neighbourhood at a time and needs no
global finiteness. Relevant names in the pinned Mathlib include
`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`,
`isClosed_of_mem_irreducibleComponents`,
`irreducibleComponent_subset_connectedComponent`,
`IsConnected.subset_connectedComponent`,
`AlgebraicGeometry.exists_isAffineOpen_mem_and_subset` and
`AlgebraicGeometry.noetherianSpace_of_isAffineOpen`. They are a guide for the
proof, not dependencies of this module.

## Imports

The module imports only Mathlib: `Mathlib.AlgebraicGeometry.Noetherian` for
`AlgebraicGeometry.IsLocallyNoetherian` and `Mathlib.Topology.Connected.Basic`
for `connectedComponent`.
