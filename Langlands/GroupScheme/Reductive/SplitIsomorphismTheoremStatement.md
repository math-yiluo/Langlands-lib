# Statement: the Isomorphism Theorem for split reductive groups

Worker 3483.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.SplitIsomorphismTheoremStatement`. The Lean file only defines the
proposition. It contains no proof of it, and it adds no other definitions, theorems or
axioms. It imports [`Reductive.RootDatum`](RootDatum.md) and Mathlib's
`Mathlib.LinearAlgebra.RootSystem.Hom`, which defines `RootPairing.Equiv`.

It is the existence part of the Isomorphism Theorem for split reductive groups (Milne,
Theorem 23.25 in its "isomorphism" form, and Remark 23.26): every isomorphism of root data
between two split reductive groups over a field comes from an isomorphism of the groups
that maps one split maximal torus onto the other.

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over:

- every field `k : Type u`. The field may be imperfect, of positive characteristic, and
  need not be separably closed;
- group schemes `G G' : GroupScheme (Spec (CommRingCat.of k))` with proofs
  `hG : IsConnectedReductive G` and `hG' : IsConnectedReductive G'`. This published
  predicate from [`Reductive.Basic`](Basic.md) says that the group is smooth, affine and
  connected over `k`, and that its base change to an algebraic closure has trivial
  unipotent radical;
- commutative group schemes `T T'` over `Spec k` with `IsSplitTorus T.toGrp` and
  `IsSplitTorus T'.toGrp`: each is isomorphic to `𝔾_m^I` for a finite index type `I`
  ([`Torus.Split`](../Torus/Split.md)). The two tori are different objects; they need
  not be equal or even have the same index type a priori;
- homomorphisms `i : T.toGrp ⟶ G` and `i' : T'.toGrp ⟶ G'` with `IsMaximalTorus i` and
  `IsMaximalTorus i'` ([`Torus.Maximal`](../Torus/Maximal.md)): each is a closed
  subgroup whose source is a torus, and it factors through no strictly larger closed
  torus of the group. So `(G, T)` and `(G', T')` are split reductive groups;
- root index types `J J' : Type u` and Mathlib integral root data
  `P : RootDatum J (characterLattice T) (cocharacterLattice T)` and
  `P' : RootDatum J' (characterLattice T') (cocharacterLattice T')` with
  `IsRootDatumOf i P` and `IsRootDatumOf i' P'`. The data live on the actual lattices
  `X^*(T) = Hom(T, 𝔾_m)` and `X_*(T) = Hom(𝔾_m, T)` of homomorphisms of commutative group
  schemes over `Spec k` ([`Torus.Lattice`](../Torus/Lattice.md)), and likewise for `T'`.
  The published predicate `IsRootDatumOf` from [`Reductive.RootDatum`](RootDatum.md) says
  three things: the pairing of the datum is the actual `latticePairing T`,
  `⟨χ, ν⟩ = gmEndEquiv k (ν ≫ χ)`, the integer of the endomorphism `ν ≫ χ` of `𝔾_m`; the
  range of its roots is the set `roots i` of the group (the nonzero characters of `T`
  with a nonzero weight space in `Lie(G)`); and each reflection `P.reflection α` is the
  action `χ ↦ σ⁻¹ ≫ χ` of some `k`-point of the group normalizing the torus through an
  automorphism `σ` of `T`;
- an equivalence of root pairings `f : RootPairing.Equiv P' P` (Mathlib,
  `LinearAlgebra/RootSystem/Hom`). It consists of
  - a `ℤ`-linear weight map `f.weightMap : X^*(T') → X^*(T)` and a `ℤ`-linear coweight
    map `f.coweightMap : X_*(T) → X_*(T')`, both bijective;
  - a bijection of index types `f.indexEquiv : J' ≃ J`;
  - the transpose condition `⟨f.weightMap χ', ν⟩_P = ⟨χ', f.coweightMap ν⟩_{P'}` for all
    `χ' ∈ X^*(T')` and `ν ∈ X_*(T)` (field `weight_coweight_transpose`);
  - `f.weightMap (P'.root j') = P.root (f.indexEquiv j')` for all `j'`
    (`root_weightMap`), and `f.coweightMap (P.coroot j) = P'.coroot (f.indexEquiv.symm j)`
    for all `j` (`coroot_coweightMap`).

`IsRootDatumOf` requires `IsAffineHom G.X.hom`. The statement supplies it as
`hG.isAffineHom` and `hG'.isAffineHom` by `haveI`, as the published
`SplitCommonTorusIsomorphismStatement` does, so no extra instance argument is introduced.

The statement assumes neither `[Finite J]` nor reducedness of `P` or `P'`. This adds no
generality beyond the source. `P.root` is injective, so `J` is in bijection with
`roots i`. Milne's root datum `R(G, T)` of a split reductive group is reduced and has a
finite set of roots (Theorem 21.11, printed pp.428–430, PDF pp.444–446, and Corollary
21.12, printed p.430; recorded in the Library as `RootDatumExistenceStatement`). Any datum
satisfying `IsRootDatumOf` has the actual roots, and its coroots are the actual coroots
(`RootDatumUniquenessStatement` in
[`Reductive.RootDatumStatement`](RootDatumStatement.md); not proved in this module). So
`P` and `P'` are Milne's root data `R(G, T)` and `R(G', T')` up to reindexing.

## Conclusion

There are an isomorphism `φ : G ≅ G'` of group schemes over `Spec k` and an isomorphism
`t : T ≅ T'` of commutative group schemes over `Spec k` such that

- `i ≫ φ.hom = CommGroupScheme.groupHom t.hom ≫ i'`: `φ` maps the torus `T` of `G` onto
  the torus `T'` of `G'`, and its restriction to `T` is `t`;
- `f.weightMap χ = t.hom ≫ χ` for every character `χ : characterLattice T'`: the weight
  map of `f` is the pullback of characters along `t`, `χ ↦ χ ∘ t`.

The conclusion constrains only the weight map of `f`. The other two components are
determined by it: `f.indexEquiv` because `P.root` is injective, and `f.coweightMap` by the
transpose condition, because the pairing of `P'` is perfect.

## Sources and provenance

The statement is derived from published results; the Lean form is not verbatim. Source:
J. S. Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups` (printed
page = PDF page − 16).

- Theorem 23.25 (Full Isogeny Theorem), printed pp.492–493 (PDF pp.508–509): "Let
  φ: (G,T) → (G',T') be an isogeny of split reductive groups over the field k; then φ
  defines an isogeny f = X(φ|T): R(G',T') → R(G,T) of root data, and every isogeny of root
  data arises in this way from an isogeny of split reductive groups; moreover, φ is
  uniquely determined by f up to an inner automorphism defined by an element of
  (T'/Z')(k). This statement also holds with "isogeny" replaced by "central isogeny",
  "Frobenius isogeny", or "isomorphism"." Its proof (same page): "Combine 23.5, 23.6,
  23.7, and 23.9."
- Remark 23.26, printed p.493 (PDF p.509): "In particular, an isomorphism φ of split
  reductive groups defines an isomorphism f of root data, and every isomorphism of root
  data f arises from a φ, unique up to the inner automorphism defined by an element of
  (T'/Z')(k). This statement is called the isomorphism theorem."
- Definition 19.22, printed p.402 (PDF p.418): a split reductive group over `k` is a pair
  `(G, T)` of a reductive group `G` over `k` and a split maximal torus `T` in `G`; a
  homomorphism `(G, T) → (G', T')` is a homomorphism `φ : G → G'` with `φ(T) ⊂ T'`. By
  6.46, printed p.135 (PDF p.151), a reductive group is smooth and connected with trivial
  geometric unipotent radical.
- Definition 23.1, printed p.483 (PDF p.499): "Let R = (X, Φ, Φ^∨) and R' = (X', Φ', Φ'^∨)
  be root data. An injective homomorphism f: X' → X with finite cokernel is an isogeny of
  root data R' → R if there exists a one-to-one correspondence α ↔ α': Φ ↔ Φ' and a map
  q: Φ → p^ℕ satisfying f(α') = q(α)α and f^∨(α^∨) = q(α)α'^∨ for all α ∈ Φ." Milne
  requires root data to be reduced (same page), and `X^∨` is the `ℤ`-linear dual of `X`.
- Definition 23.2, printed p.484 (PDF p.500): "An isogeny f of root data is central if
  q(α) = 1 for all α ∈ Φ; it is an isomorphism if it is central and f is an isomorphism of
  ℤ-modules. Thus an isomorphism f: X' → X of ℤ-modules is an isomorphism of root data if
  and only if there exists a one-to-one correspondence α ↔ α': Φ ↔ Φ' such that f(α') = α
  and f^∨(α^∨) = α'^∨ for all α ∈ Φ."

**Translation.** The statement is the existence part of Remark 23.26 for the split
reductive groups `(G, T)` and `(G', T')`.

- *The setting.* `IsConnectedReductive` matches 6.46, and the split maximal tori `i`, `i'`
  make `(G, T)` and `(G', T')` split reductive groups in the sense of Definition 19.22.
- *The isomorphism of root data.* Milne's `R(G', T') → R(G, T)` is a `ℤ`-isomorphism
  `f : X^*(T') → X^*(T)` with a bijection `α ↔ α'` of roots such that `f(α') = α` and
  `f^∨(α^∨) = α'^∨`, where `f^∨ : X_*(T) → X_*(T')` is the transpose of `f`. An
  equivalence `RootPairing.Equiv P' P` gives exactly this: its weight map is a bijective
  linear `f`; its coweight map is the transpose of `f` (transpose condition); and its
  index bijection, read through the injective root maps of `P'` and `P` whose ranges are
  the actual root sets, is a bijection `α' ↔ α` with `f(α') = α` (`root_weightMap`) and
  `f^∨(α^∨) = α'^∨` (`coroot_coweightMap`), the coroots being the actual coroots.
  Conversely, an isomorphism of root data in Milne's sense yields such an equivalence:
  the index bijection is the root bijection read through `P'.root` and `P.root`, and the
  coweight map is the transpose of `f`, which exists and is bijective because the
  pairings of `P` and `P'` are perfect.
- *The conclusion.* Remark 23.26 gives an isomorphism `φ : (G, T) → (G', T')` of split
  reductive groups with `X(φ|T) = f`, where `X(φ|T)` sends `χ ∈ X^*(T')` to `χ ∘ φ|T`.
  Since `φ` is an isomorphism with `φ(T) ⊂ T'` and `X(φ|T) = f` is bijective, `φ|T` is an
  isomorphism `t : T → T'` (Theorem 12.9(a), printed p.233, PDF p.249: `X` is an
  anti-equivalence on diagonalizable groups). So `φ ∘ i = i' ∘ t` and `f(χ) = χ ∘ t`,
  which is the Lean conclusion with `φ.hom = φ` and `t.hom = t`. Conversely the Lean
  conclusion says that `φ` maps `T` onto `T'` through `t`, so `φ` is an isomorphism of
  split reductive groups with `X(φ|T) = f`.
- *Omitted parts.* The uniqueness of `φ` up to the inner automorphism defined by an
  element of `(T'/Z')(k)` and the converse direction (an isomorphism of split reductive
  groups defines an isomorphism of root data) are not included.

**Errata.** The official errata snapshot
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for printed pp.135, 233,
402, 428–430, 483, 484, 492 or 493. Its Chapter 23 entries start at p.488 (proof of 23.11,
`U_{α₂}` changed to `U_{α₂}(k)`), which lies inside the proof of the Isogeny Theorem, not in
the statements used here.

## Relation to the Library

- [`Reductive.SplitIsomorphismStatement`](SplitIsomorphismStatement.md) records
  `SplitCommonTorusIsomorphismStatement`, the case in which the two groups share one split
  maximal torus `T` and the isomorphism of root data is the identity of `X^*(T)`. Its
  ledger row notes that the general isomorphism of root data is not covered there. The
  present statement allows different tori and an arbitrary equivalence `f`. For `T' = T`
  and `f` with identity weight and coweight maps, its conclusion gives `t` with
  `t.hom ≫ χ = χ` for all characters, hence `t` is the identity of `T`
  (`IsSplitTorus.hom_ext_of_characters` in
  [`Torus.CharacterIsomorphism`](../Torus/CharacterIsomorphism.md)) and `i ≫ φ.hom = i'`.
- [`Reductive.PinnedIsomorphismStatement`](PinnedIsomorphismStatement.md) records
  `PinnedIsomorphismStatement`, the pinned version: groups with pinnings and an
  equivalence of root data that maps base onto base, with a unique pinned lift. The
  present statement needs no pinning, and `f` need not respect any base.
- [`Reductive.LocalSplitIsomorphismTheoremStatement`](LocalSplitIsomorphismTheoremStatement.md)
  records an isomorphism theorem over local rings for coordinate split tori, whose
  conclusion is only `Nonempty (G ≅ H)`.

This module proves none of these statements and none of their relations.
