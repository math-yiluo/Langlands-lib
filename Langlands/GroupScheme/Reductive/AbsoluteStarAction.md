# Galois pinning data for every connected reductive group, and the absolute star action

Author: Worker 15, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483).

The module `Reductive/StarAction` constructs the star action from supplied
`GaloisPinningData k E G`. This module constructs such data for every connected
reductive group over a field. It uses the separable closure, and so gives the star
action of the absolute Galois group. Every construction is assembled from published
Library theorems, and no hypothesis is added.

## Constructions and lemmas

Let `k : Type u` be a field and `G` a group scheme over `Spec k` with affine structure
morphism and `hG : IsConnectedReductive G`. Write `k_s = SeparableClosure k`, Mathlib's
separable closure of `k` inside `AlgebraicClosure k`.

- `GaloisPinningData.isSplitTorus_separableClosure`: if `T` is a torus over `k`
  (`IsTorus`), then `T_{k_s}` is a split torus. Proof: the published
  `torusFiniteGaloisSplitting` gives a finite Galois extension `K` over which `T`
  splits. Mathlib's `IsSepClosed.lift` embeds `K` into `k_s` over `k`. The base change
  of a split torus is split (`IsSplitTorus.baseChange`), and
  `GroupScheme.baseChangeCompIso` identifies the base change along `k → K → k_s` with
  the base change along `k → k_s`.
- `GaloisPinningData.ofSeparableClosure hG : GaloisPinningData k k_s G`. The steps are:
  1. `maximalTorusExistence` chooses a maximal torus `i : T ⟶ G` over `k`.
  2. `T_{k_s}` is split by the previous lemma. `G_{k_s}` is connected reductive by
     `connectedReductiveFieldExtensionStatement`. `i_{k_s}` is maximal by
     `maximalTorusBaseChange`.
  3. `rootDatumExistence` chooses a reduced root datum of `(G_{k_s}, T_{k_s})`.
  4. The base is the one constructed by `Langlands.LinearAlgebra.RootDatumBase.base`,
     as in `SplitPinning.ofRootDatum`.
  5. The simple-root Lie vectors are `RootPinning.ofSplitMaximalTorus`.
- `GaloisPinningData.exists_finiteGalois hG`: the same data exist over some field `E`
  finite-dimensional and Galois over `k`. The splitting field is the one given by
  `torusFiniteGaloisSplitting`.
- `absoluteStarAction hG` (with `[LocallyOfFiniteType G.X.hom]`) is
  `(GaloisPinningData.ofSeparableClosure hG).starAction`. It is a monoid homomorphism
  from `k_s ≃ₐ[k] k_s`, the absolute Galois group of `k`, to the automorphisms of the
  based root datum of `(G_{k_s}, T_{k_s})` preserving the chosen base.

The private helper `ofSplittingField` assembles the data from a maximal torus over `k`
and any field over which it splits. It is shared by the last two items.

## Source

Milne, *Algebraic Groups* (2022 corrected reprint), source `milne-2022-algebraic-groups`,
SHA-256 `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`, §25.c,
printed p.555 (PDF p.566). Milne takes a maximal torus `T` of `G` over `k`, notes that
"`(G, T)_{k_s}` is split", forms the based root datum of `(G_{k_s}, B, T_{k_s})`, and
defines the `*`-action of `Γ = Gal(k_s/k)` on it. `absoluteStarAction` is this
construction, with the base given by the chosen `RootDatumBase.base` in place of a
Borel subgroup `B`. Milne's maximal torus contains a maximal split torus, which matters
only for the Tits index. The torus here is any maximal torus over `k`.

The constructions use `Classical.choice` for the maximal torus, the root datum and the
pinning. Independence of these choices, up to the isomorphisms induced by
`G(k_s)`-conjugation, is the separate `StarActionIndependenceStatement`.
