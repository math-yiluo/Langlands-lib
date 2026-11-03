# Properness transfer to quotients by open subgroups of stabilizers

Authors: Worker 716, with the interface agreed with Worker 1293 (who added the
closedness requirement on `iH`) and Worker 898.

This pair states one proposition, `FiniteIndexQuotientProperTransferStatement`,
at arbitrary universe `u`. It is not proved here; its proof is a separate
obligation.

## Statement

Fix an algebraically closed field `k : Type u` and a smooth affine group scheme
`G` over `Spec k` (`Smooth G.X.hom`, `IsAffineHom G.X.hom`). The data are:

- a closed subgroup `iS : S ⟶ G` (`IsClosedSubgroup iS`, the underlying
  morphism is a closed immersion). `S` may be nonreduced or disconnected;
- a closed subgroup `iH : H ⟶ G` (`IsClosedSubgroup iH`) with a homomorphism
  `f : H ⟶ S` such that `f ≫ iS = iH`, and such that the image of the
  underlying map of `f` is an open subset of the topological space of `S`;
- a scheme `O` over `k` with `IsProper O.hom`, and a morphism `π : G.X ⟶ O`
  over `k` such that `π.left` is flat, surjective and quasi-compact. On every
  test scheme `T` over `k`, two points `g, h ∈ G(T)` satisfy `g ≫ π = h ≫ π`
  exactly when `g⁻¹ * h` lies in `SubgroupFunctor.range iS` at `T`.

The proposition asserts the following. Let `Q` be a scheme over `k` with
`IsSeparated Q.hom`, `LocallyOfFiniteType Q.hom` and `QuasiCompact Q.hom`. Let
`q : G.X ⟶ Q` be a morphism over `k` with `q.left` smooth, surjective and
quasi-compact, such that on every test scheme `T` over `k`, `g ≫ q = h ≫ q`
holds exactly when `g⁻¹ * h` lies in `SubgroupFunctor.range iH` at `T`. Then
`IsProper Q.hom`.

The fiber conditions are those of
`Langlands.GroupScheme.SmoothSubgroupQuotientExistenceStatement` and
`Langlands.GroupScheme.ParabolicSubgroupQuotientProperStatement` in
`Langlands.GroupScheme.HomogeneousQuotientStatement`. Test schemes are
arbitrary schemes over `k`, not only affine or reduced ones. The orientation
is that of the cosets `gS` and `gH`, called right cosets in that module. So
`(O, π)` is a quotient model for `G` by `S`, and `(Q, q)` one for `G` by `H`.

## Meaning of the hypotheses

The openness of the image of `f` is the topological form of the situation
`H = ((S_red)°)`: `H` is a closed subgroup of `S` whose underlying set is open.
As `S` is of finite type over the algebraically closed field `k`, its
underlying set is then a union of finitely many translates of that of `H` by
rational points. No smoothness, connectedness or reducedness of `S` is assumed. In
characteristic `p` the scheme-theoretic stabilizer `S` of a point of a flag
variety can be nonreduced. In that case `G → G/S` is flat but not smooth,
which is why `π` is only required to be flat. Smoothness of `H` is not
assumed either. The hypotheses on `q` are kept exactly as in the published
quotient statements, so that every supplied model for `G` by a Borel subgroup
can be fed in unchanged.

`IsClosedSubgroup iH` is stated as a separate hypothesis. Openness of the
image of `f` alone says nothing about scheme structure. Together with closedness
of `iS` and `f ≫ iS = iH`, it makes `f` itself a closed immersion.

Algebraic closedness of `k` is part of the intended use: the consumer route is
the some-Borel interface
`Langlands.GroupScheme.SomeBorelQuotientProperStatement` (task
`e5a45569-12db-447b-a313-75bb782291d2`) over algebraically closed fields.
Closed points of finite-type `k`-schemes are then rational, so the translates
covering `S` can be taken by rational points.

The proposition has no conclusion about existence of `Q` or `O`. Both models
are supplied, and the conclusion concerns the same supplied `Q`.

## Provenance

This is a derived formulation. It is not a verbatim result of the registered
original, J. S. Milne, *Algebraic Groups* (2017), source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. It is the
finite-map step needed when a closed orbit `G·y` in a flag variety has a
possibly nonreduced or disconnected stabilizer `S` with `(S_red)° = B`.

- Milne Definition 5.20 and Propositions 5.21–5.22, printed p.104, define a
  quotient of `G` by a subgroup through its orbit map. A morphism constant on
  cosets factors through the quotient, so `G/H → G/S` exists for `H ⊆ S`.
- Milne Propositions 5.24–5.25, printed pp.104–105: `G × H ≅ G ×_{G/H} G` and
  `G → G/H` is faithfully flat. This is the flat presentation that the
  all-test fiber condition and the flatness of `π` express here.
- Milne Appendix A.75–A.76, printed p.583: completeness of an algebraic
  scheme is properness of its structure map, finite maps are proper (A.76(a)),
  and a scheme proper over a complete scheme is complete (A.76(c)).

Classically, under these hypotheses `G/H → G/S` has finite fibers `S/H` and
is proper. With
`O ≅ G/S` proper, this gives properness of `Q ≅ G/H`. The proof of that step,
including the comparison of the supplied models, is the separate proof
obligation; nothing here assumes it.

The full registered author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read. No entry concerns
5.20–5.25 or A.75–A.76. The erratum to A.70 (generic flatness gives a flat,
not a faithfully flat, map over a dense open) matters only to a consumer that
proves flatness of an orbit map. It does not change this statement.
