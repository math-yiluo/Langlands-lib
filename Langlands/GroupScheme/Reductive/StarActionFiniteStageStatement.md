# The star action over the separable closure is realized at a finite Galois stage: statement

Author: Worker 93, for Task 5703 (`897f230f-d15d-48df-9d7a-63d2e4635fa8`). The module
contains one `Prop`-valued definition and no proof. It concerns `GaloisPinningData` and
`GaloisPinningData.starAction` of the module `Reductive/StarAction`, and is shaped like the
published `StarActionIndependenceStatement` (module `Reductive/StarActionStatement`).

The module also declares a local instance `starActionFiniteStageBaseChangeAffine`: the base
change of `G` along `algebraBaseMap k E` has affine structure morphism. It is a copy of the
local instance of the same content in `Reductive/StarActionStatement`, needed to form
`toSplitPinning` of the data; it is not exported.

## Statement

`Langlands.GroupScheme.StarActionFiniteStageStatement.{u}` quantifies over a field
`k : Type u` and a group scheme `G` over `Spec k` whose structure morphism is affine and
locally of finite type, and over Galois pinning data
`d : GaloisPinningData k (SeparableClosure k) G` over the separable closure `k_s` of `k`.
It asserts that there exist

- a field `L : Type u` with a `k`-algebra structure, finite-dimensional and Galois over `k`;
- a `k`-algebra embedding `ι : L →ₐ[k] SeparableClosure k`;
- Galois pinning data `d' : GaloisPinningData k L G` over `L`;
- an equivalence `e : RootPairing.Equiv P' P` from the root datum `P'` of `d'` (the root datum
  of `(G_L, T'_L)`) to the root datum `P` of `d` (the root datum of `(G_{k_s}, T_{k_s})`);

such that

1. the root bijection `e.indexEquiv` carries the support of the base of `d'` exactly onto the
   support of the base of `d`: `a ∈ base' ↔ e.indexEquiv a ∈ base`;
2. for every `σ : L ≃ₐ[k] L` and every `τ : k_s ≃ₐ[k] k_s` with `τ (ι x) = ι (σ x)` for all
   `x : L` (that is, `τ` restricts to `σ` along `ι`),
   `e ∘ starAction_{d'} σ = starAction_d τ ∘ e` as equivalences `P' ≃ P`
   (`RootPairing.Equiv.comp e (d'.starAction σ).val = RootPairing.Equiv.comp (d.starAction τ).val e`).

So the based root datum of `G` and its star action by the absolute Galois group, which the
published `TitsIndexData` carries over `k_s`, are already realized over a finite Galois
extension `L` inside `k_s`. In particular the star action of every `τ` depends only on the
restriction of `τ` to `ι(L)`. If the star action of every `τ` is trivial then so is the star
action of every `σ ∈ Gal(L/k)`: each `σ` is the restriction of some `τ`, because `L/k` is
normal and `k_s/k` is algebraic.

The statement requires nothing of `d'` beyond being Galois pinning data over `L`. Its torus is
defined over `k` and its base change to `L` is a split maximal torus. The intended proof
takes the torus `T` of `d`, which is defined over `k` and splits over `k_s`, and lets `L` be a
finite Galois splitting field of `T` inside `k_s`. The root datum, base and simple-root Lie
vectors of `G_{k_s}` then descend to `G_L`, and the Galois actions on the character lattices
of `T_L` and `T_{k_s}` are compatible under restriction. These are proof obligations.

## Role

This is one of the prerequisites in the planned proof of `InnerTypeANormOneStatement`
(Task 5703). Inner type is a condition on the star action over `k_s`. The published
inner-twist machinery (`IsAdjointQuotient.hasInnerDiscrepancy_of_galois_baseChange`,
`QuasiSplitInnerForm.ofInnerDiscrepancy`) needs pinning data and Galois elements over a
finite Galois extension. This statement connects the two.

## Source and provenance

Provenance: derived.

J. Tits, *Classification of algebraic semisimple groups*, in *Algebraic Groups and
Discontinuous Subgroups*, Proc. Sympos. Pure Math. 9, AMS, 1966, pp.33–62, source
`tits-1966-classification-algebraic-semisimple`, SHA-256
`962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`, §2.3, printed p.39
(PDF p.44). Tits defines the `*`-action of `Γ = Gal(K/k)` (`K` a separable closure) on the
simple roots `Δ` of `G` with respect to a maximal torus `T` defined over `k`: "since `K` is
separably closed, `T` is split over `K`, therefore all its characters are defined over `K`
and `Γ` operates naturally on `X*(T)`; then, `σ(Δ)` is the system of simple roots for a
certain ordering of `X*(T)`, there exists a well-defined element `w` of the Weyl group for
which `w(σ(Δ)) = Δ`, and we set `σ* = w ∘ σ`." He adds that in practice the full action is
known once "the group `{σ | σ* = id}` (or, equivalently, the fixed field of this group)" is
known.

The statement is derived from this definition. The same construction applies over any
splitting field of `T`. Since `T` splits over a finite Galois extension `L ⊆ K`, the
`*`-action of `Γ` factors through `Gal(L/k)`, and is the `*`-action computed over `L`. Tits
uses this implicitly when he speaks of the fixed field. The Lean statement makes the finite
stage explicit through actual Galois pinning data over `L` and an isomorphism of based root
data. It is formulated like `StarActionIndependenceStatement`.
