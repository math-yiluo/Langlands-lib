# Simply connected groups of type `C_n` are inner forms of `Sp_{2n}`: proof

Proof of `Langlands.GroupScheme.TypeCQuasiSplitInnerFormStatement` (module
`Langlands.GroupScheme.SimplyConnected.TypeCQuasiSplitInnerFormStatement`):

```lean
theorem typeCQuasiSplitInnerForm : TypeCQuasiSplitInnerFormStatement.{u}
```

Author: Worker 31, for Task 5986 (`8494af77-9d10-4c2f-b1cd-60dc371fb195`). The route follows
Worker 93's published reduction `InnerTypeANormOneReduction` (Task 5703), which proves the
analogous statement for inner type `A`. The proof imports two of its lemmas and the published
module `Langlands.GroupScheme.SimplyConnected.TrivialStarInnerTwist`. The theorem has exactly the
published statement as its type at every universe `u`, with no additional premise, over every
field. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Statement

For a field `K`, an affine, locally finite type group scheme `G` over `Spec K`, actual index
data `d : TitsIndexData G`, and `e : d.Vertex ≃ Fin n` with `2 ≤ n` and
`d.cartan a b = CartanMatrix.C n (e a) (e b)`, if `G` is simply connected then there is
`q : QuasiSplitInnerForm G` with `Nonempty (q.model ≅ Symplectic.groupScheme K n)`.

## Helper results (namespace `TypeCQuasiSplitInnerFormProof`)

- `Langlands.CartanCNumbering.rigid`: for `2 ≤ n`, a map `f : Fin n → Fin n` with
  `C_n(f i, f j) = C_n(i, j)` for all `i, j` is the identity. It is injective, since
  `C_n(i, j) = 2` only for `i = j`. The proof is by downward induction on `i`. The last vertex
  `n - 1` is the only row containing an entry `-2` (at `n - 2`), so `f` fixes it. If `f`
  fixes every vertex after `i < n - 1`, then `C_n(f i, i + 1) = C_n(i, i + 1) = -1`, so `f i`
  is `i` or `i + 2`. The value `i + 2 = f(i + 2)` is excluded by injectivity.
- `cartan_star`: the full star action preserves `d.cartan`. It acts by root-datum
  automorphisms (Mathlib's `RootPairing.Hom.pairing`).
- `star_eq_self`: under the type-`C_n` hypothesis, `d.star σ a = a` for every Galois
  element `σ` and vertex `a`. Apply `Langlands.CartanCNumbering.rigid` to the star permutation transported
  along `e`.

## Published lemmas used

- `Langlands.LinearAlgebra.SimplyConnectedRootDatum.corootSpan_eq_top_of_equiv`: spanning
  coroots are preserved by equivalences of root data.
- `InnerTypeANormOneReduction.finiteStage_starAction_eq_one`: the star action over the finite
  Galois stage of `StarActionFiniteStageStatement` is trivial when the absolute star action
  fixes every simple vertex.

## Proof of the main theorem

1. **Finite Galois stage.** The published `starActionFiniteStage` applied to `d.pinning` gives
   a finite Galois extension `L/K`, `ι : L →ₐ[K] K_s`, Galois pinning data `d'` of `G` over
   `L`, and a base-preserving equivalence `e` from the root datum of `d'` to that of
   `d.pinning`, which intertwines the star actions.
2. **Spanning coroots over `L`.** `G_L` is simply connected
   (`isSimplyConnectedFieldExtension`), so the coroots of `d'` span the cocharacter lattice
   (`splitSimplyConnectedCorootSpan`).
3. **Trivial star action over `L`.** By `star_eq_self`, the absolute star action fixes every
   simple vertex. So `d'.starAction σ = 1` for every `σ ∈ Aut_K(L)`
   (`finiteStage_starAction_eq_one`).
4. **Split model.** `SymplecticMatrix.TypeCPinning.exists_splitPinning n K` gives a split
   pinning `p` of `Sp_{2n} = SymplecticMatrix.groupScheme (Fin n) K` with spanning coroots and
   type-`C_n` numbering `e1`. Its base change `pL` to `L` has an equivalent root datum
   (`baseChangeRootDatumEquiv`), hence spanning coroots, and the same simple roots
   (`baseChangeSimpleEquiv`).
5. **Matching simple roots.** The bijection `e2` from the simple roots of `pL` to those of
   `d'` is the composite of `baseChangeSimpleEquiv⁻¹`, `e1`, `e⁻¹` (the numbering of `d`)
   and the inverse restriction of the stage equivalence. It preserves simple pairings: those
   of `d'` equal those of `d` (`RootPairing.Hom.pairing`), which are `CartanMatrix.C n` under
   the numbering, which is the matrix of `p` under `e1`, which equals that of `pL`.
6. **Root-datum isomorphism.** The published `corootSpanCartanEquiv` gives an equivalence
   `f` of root data extending `e2`. It maps the base support onto the base support.
7. **Pinned isomorphism.** The published `pinnedIsomorphism` gives a pinned isomorphism
   `E : pL ≅ d'`, in particular `E.groupIso : Sp_{2n,L} ≅ G_L`.
8. **Inner form.** Choose an adjoint quotient `q` of `Sp_{2n}` (`adjointQuotientExistence`).
   The split group is quasi-split (`p.isQuasiSplit`), and so is its adjoint quotient
   (`adjointQuotientQuasiSplitStatement`). `TrivialStarInnerTwist.hasInnerDiscrepancy`, with
   step 3, shows that `LocalGroupIso.ofBaseChangeIso E.groupIso` has inner discrepancy.
   `QuasiSplitInnerForm.ofInnerDiscrepancy` then builds a quasi-split inner-form presentation
   of `G` whose model is `SymplecticMatrix.groupScheme (Fin n) K`.
9. **Model.** `SymplecticMatrix.comparisonIso K n` identifies this model with
   `Symplectic.groupScheme K n`.

The hypothesis `2 ≤ n` is used only in `Langlands.CartanCNumbering.rigid`.

## Literature

The classical argument: the Dynkin diagram of type `C_n`, `n ≥ 2`, has no nontrivial
automorphism, so a group of type `C_n` has trivial star action and is an inner form of its
quasi-split, here split, form (Tits 1966, §2.3, printed p.39, and Table II, type `C_n`,
printed p.56, source `tits-1966-classification-algebraic-semisimple`). Knus–Merkurjev–Rost–
Tignol, Theorem (26.14), printed p.369 (source
`knus-merkurjev-rost-tignol-1998-book-of-involutions`), use the same twisting description of
simply connected groups of type `C_n`. The Lean proof is a direct verification at a finite
Galois stage. It uses the published isomorphism theorem for split pinned groups and the
type-`C_n` pinning of `Sp_{2n}` from the published module
`SymplecticMatrix.TypeCPinning`.

The Cartan rigidity lemma is reused from
[CartanCNumbering](../../LinearAlgebra/CartanCNumbering.md); this module does not duplicate its proof.
