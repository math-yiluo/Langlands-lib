# Proof that connected components of a locally Noetherian scheme are open

The theorem
`Langlands.AlgebraicGeometry.locallyNoetherianConnectedComponentOpen_proof.{u}`
proves the published proposition
`Langlands.AlgebraicGeometry.LocallyNoetherianConnectedComponentOpenStatement.{u}`,
imported unchanged from
`Langlands.AlgebraicGeometry.LocallyNoetherianConnectedComponentOpenStatement`.
Its type is exactly that proposition, at an arbitrary universe `u`:

```lean
∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]
  (x : X), IsOpen (connectedComponent x)
```

The proof adds no hypotheses. The scheme need not be quasi-compact, globally
Noetherian, separated, reduced or defined over a field. No
`LocallyConnectedSpace` instance is assumed or constructed, and Mathlib's
`isOpen_connectedComponent` is not used. The proof works directly with Mathlib's
`connectedComponent` in the underlying topological space of `X`.

## Implemented proof

### Helper: Noetherian topological spaces

`Langlands.AlgebraicGeometry.isOpen_connectedComponent_of_noetherianSpace`
states that every connected component of a Noetherian topological space is
open:

```lean
theorem isOpen_connectedComponent_of_noetherianSpace {α : Type*}
    [TopologicalSpace α] [NoetherianSpace α] (x : α) :
    IsOpen (connectedComponent x)
```

Its proof lets `S` be the set of irreducible components of `α` that are
disjoint from `connectedComponent x`.

- `S` is finite because it is a subset of the irreducible components, which are
  finite by `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`.
  Each member is closed by `isClosed_of_mem_irreducibleComponents`. Hence the
  union `⋃₀ S` is closed (`Set.Finite.isClosed_sUnion`).
- The proof then shows that `connectedComponent x` is the complement of
  `⋃₀ S`. A point of the connected component lies in no member of `S`, because
  every member is disjoint from the component. Conversely, let `y` be outside
  `connectedComponent x`. Then `connectedComponent y` differs from
  `connectedComponent x`, since `y` lies in its own component. By
  `connectedComponent_disjoint` the two components are disjoint. The
  irreducible component `irreducibleComponent y` is an irreducible component
  (`irreducibleComponent_mem_irreducibleComponents`). It contains `y`
  (`mem_irreducibleComponent`) and lies inside `connectedComponent y`
  (`irreducibleComponent_subset_connectedComponent`). So it is a member of `S`
  containing `y`, and `y` lies in `⋃₀ S`.

The connected component is therefore the complement of a closed set, hence
open.

### Main theorem

Fix a locally Noetherian scheme `X` and a point `x`. By
`isOpen_iff_forall_mem_open`, it suffices to give each point `y` of
`connectedComponent x` an open set containing `y` and contained in
`connectedComponent x`.

1. `AlgebraicGeometry.exists_isAffineOpen_mem_and_subset`, applied inside the
   whole space, gives an affine open `U : X.Opens` containing `y`.
2. Local Noetherianity, through `IsLocallyNoetherian.component_noetherian`,
   makes the ring of sections `Γ(X, U)` Noetherian. Then
   `AlgebraicGeometry.noetherianSpace_of_isAffineOpen` makes the subspace `U` a
   Noetherian topological space. This instance is passed explicitly to the
   helper because instance search does not use the local hypothesis for the
   subtype `↥U`.
3. Let `y'` be `y` regarded as a point of `U`. The helper shows that
   `connectedComponent y'`, taken in the subspace `U`, is open in `U`. Since `U`
   is open in `X`, the inclusion map is an open map
   (`IsOpen.isOpenMap_subtype_val`). Thus the image
   `Subtype.val '' connectedComponent y'` is open in `X`. It contains `y`.
4. This image is connected, being the image of a connected set under the
   continuous inclusion. It contains `y`, so
   `IsConnected.subset_connectedComponent` places it inside
   `connectedComponent y`. Because `y ∈ connectedComponent x`,
   `connectedComponent_eq` identifies `connectedComponent x` with
   `connectedComponent y`. Hence the image lies in `connectedComponent x`.

Thus every point of `connectedComponent x` has an open neighbourhood inside the
component, and the component is open.

Local Noetherianity is used only on one affine open neighbourhood at a time.
The argument uses no finite affine cover and no global finiteness.

## Checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled
this module without errors or warnings. Inspection of
`locallyNoetherianConnectedComponentOpen_proof` reports a theorem with universe
parameter `u`. It depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. No `sorry`, `admit` or new axiom is used.

## Provenance and authorship

The proof follows the route suggested in the statement's Markdown and in the
proof task context. That route is a standard topology argument, not taken from a
cited proof. The statement itself is derived from Edixhoven, van der Geer and
Moonen, *Abelian Varieties* (preliminary draft), paragraph (3.16), printed p.38
(PDF p.42), literature ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`. That source only asserts
the implication "locally Noetherian, hence locally connected" and gives no proof
of it. This module does not follow or claim a route from the source.

The helper `isOpen_connectedComponent_of_noetherianSpace` is an internal general
topology lemma written for this proof. The pinned Mathlib has no lemma with this
statement. Mathlib's `isOpen_connectedComponent` requires a
`LocallyConnectedSpace` instance, which Mathlib does not supply for Noetherian
spaces or locally Noetherian schemes. All other names cited above are existing
Mathlib declarations.

Author: Worker 747.

## Imports

- `Langlands.AlgebraicGeometry.LocallyNoetherianConnectedComponentOpenStatement`,
  the target proposition, which also brings in
  `Mathlib.AlgebraicGeometry.Noetherian` and `Mathlib.Topology.Connected.Basic`.
- `Mathlib.Topology.NoetherianSpace`, for Noetherian topological spaces and
  their finitely many irreducible components.
