# Connected reductive groups without roots

This internal supporting unit proves the rank-zero case of
`SplitRankOneCommonTorusIsomorphismStatement` (Milne, *Algebraic Groups*,
2017, Proposition 23.14, in the degenerate case where the root system is
empty). It contains three results.

## `IsConnectedReductive.isIso_of_roots_eq_empty`

Let `i : T ⟶ G` be a maximal torus of a connected reductive group `G` over a
field `k`, with `T` split. If `roots i = ∅`, then `i` is an isomorphism.

The proof follows the standard argument (Milne 17.61(a)/17.84 in the central
case) and uses only proved Library results:

1. `isCentral_of_roots_eq_empty` makes `i` central, since an empty root set
   makes the adjoint action of `T` on the Lie algebra trivial.
2. Let `b` be the base change to the algebraic closure `k̄` of `k`.
   `IsCentral.baseChange` keeps the base change of `i` central.
   `centralMaximalTorusBaseChangeReduction`, fed with the proved
   `normalSubgroupQuotient`, `centralMaximalTorusQuotientStatement` and
   `noTorusBaseChangeReduction noTorusUnipotent`, keeps it a maximal torus.
3. `IsConnectedReductive.baseChange_toAlgebraicClosure` makes the base change
   of `G` connected reductive. Then
   `IsConnectedReductive.isIso_of_isCentral_of_isMaximalTorus`, fed with the
   proved `noTorusUnipotent` (Milne 17.81) and `solvableTorusQuotient`
   (Milne 16.33), shows that the base change of `i` is an isomorphism.
4. A field extension is fpqc (`fieldExtension_fpqc`), so
   `isIso_of_baseChange` shows that `i` itself is an isomorphism.

## `roots_eq_of_isRootDatumOf_of_reindex`

If `P₁` is a root datum of `i₁`, `P₂` a root datum of `i₂` (in the sense of
`IsRootDatumOf`), and `e : J₁ ≃ J₂` satisfies `P₂.root ∘ e = P₁.root`, then
`roots i₂ = roots i₁`. Both sets equal the range of the root map, and
reindexing by a bijection does not change that range.

## `exists_iso_of_roots_eq_empty`

This is the rank-zero branch of the target statement. Under the hypotheses
of `SplitRankOneCommonTorusIsomorphismStatement` that concern roots (the
coroot matching and the rank-one hypothesis are not needed), if
`roots i₁ = ∅` then `roots i₂ = ∅` too. Both `i₁` and `i₂` are then
isomorphisms by the first result, and `ψ = i₁⁻¹ ≫ i₂` satisfies
`i₁ ≫ ψ = i₂`.
