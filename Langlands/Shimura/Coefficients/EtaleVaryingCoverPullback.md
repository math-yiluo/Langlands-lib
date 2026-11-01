# Etale base change of varying-cover coefficient cospans

This internal construction assembles the constant-module associated-sheaf
comparison and its cross-cover compatibility for an entire varying-group
coefficient diagram. It compares the actual transition cospans on the original
scheme with those on the geometrically base-changed cover diagram.

The schemes, coefficient ring, module carriers and deck-group carriers share a
universe `u`. The index category has independent object and morphism universes
`uI` and `vI`. The base morphism `f : Z ⟶ X` is etale. The group diagram is
`D : I ⥤ GrpCat`, and `Y : EquivariantDiagram D X.Etale` is arbitrary: there is
no finiteness, surjectivity or torsor hypothesis.

## Construction

For an index `i`, `etaleAssociatedAtPullback` is the natural isomorphism

```text
etaleAssociatedAt X Y i ⋙ restriction f
  ≅ etaleAssociatedAt Z ((etaleTorsorDiagramPullback f D).obj Y) i.
```

It is obtained by whiskering `etaleConstantAssociatedPullback` with evaluation
of the coefficient diagram at `i`. The target cover is the actual scheme fiber
product, with its induced deck action and geometrically pulled-back transitions.

For `b : i ⟶ j`, the common cospan target uses the cover `Y.action i` and the
coefficient representation `M.action j` restricted along `(D.map b).hom`.
`etaleAssociatedTransitionTargetPullback` is the same comparison whiskered with
evaluation at `j` and this group restriction. All three endpoints are therefore
natural in the whole category `EquivariantDiagram D (ModuleCat R)`.

Write `T` for etale restriction, `A_i` and `A_j` for the two associated endpoint
sheaves, and `B_b` for the common target. Let `q_i`, `q_j`, `q_b` denote the
forward comparisons with the corresponding sheaves after base change.
`etaleAssociatedReduction_pullback` and `etaleAssociatedComparison_pullback`
prove the two equations

```text
T(reduction_b) ≫ q_b = q_i ≫ reduction'_b,
T(comparison_b) ≫ q_b = q_j ≫ comparison'_b.
```

The first equation is naturality of the constant-associated comparison for
`M.transition b`. The second is the previously proved cross-cover compatibility
with identity coefficient map. In particular the new cospan legs are the actual
coefficient-reduction and cover-change maps; no output square is supplied as a
hypothesis.

`etaleAssociatedTransitionCospanPullback` packages these equations as a natural
isomorphism

```text
etaleAssociatedTransitionCospan X Y b ⋙ postcompose (restriction f)
  ≅ etaleAssociatedTransitionCospan Z
      ((etaleTorsorDiagramPullback f D).obj Y) b.
```

The Lean construction uses `cospanIsoMk` at each coefficient diagram. Naturality
in a coefficient-diagram morphism follows at the three vertices from the two
endpoint natural isomorphisms. The six endpoint lemmas identify the forward
and inverse maps at `left`, `right` and `one` with the original
`etaleConstantAssociatedPullback` components, including the group restriction
at `one`.

## Provenance and scope

This is a derived internal categorical construction from the imported
`VaryingCover`, `EtaleTorsorPullback`, `EtaleConstantAssociatedPullback` and
`EtaleCrossCoverPullback` interfaces and Mathlib's cospan constructor. It claims
no additional theorem of Harris.

The result concerns each index arrow and is natural in every coefficient
diagram. It does not invert the cover-comparison leg, assert coherence between
different index arrows, or compare iterated geometric base changes. The
finite-torsor varying-system comparison, arbitrary non-etale inverse image,
actual Harris geometry, compact supports, limits and cohomological comparisons
remain separate constructions.
