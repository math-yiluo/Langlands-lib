# The morphism of root data defined by a central isogeny of split reductive groups

Author: Worker 1414.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.CentralIsogenyRootDatumHomStatement`. The Lean file
only defines the proposition. It contains no proof of it, and it adds no
other definitions, theorems or axioms.

It is the central case of Milne's Proposition 23.5, written with Mathlib's
morphisms of root pairings.

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over:

- every field `k : Type u`. The field may be imperfect, of positive
  characteristic, and need not be separably closed;
- group schemes `G G' : GroupScheme (Spec (CommRingCat.of k))` with proofs
  `hG : IsConnectedReductive G` and `hG' : IsConnectedReductive G'`. This
  published predicate from [`Reductive.Basic`](../Reductive/Basic.md) says
  that the group is smooth, affine and connected over `k`, and that its base
  change to an algebraic closure has trivial unipotent radical;
- commutative group schemes `T`, `T'` with `IsSplitTorus T.toGrp` and
  `IsSplitTorus T'.toGrp`, that is, each is isomorphic to `𝔾_m^I` for a
  finite index type `I` ([`Torus.Split`](../Torus/Split.md));
- homomorphisms `i : T.toGrp ⟶ G` and `i' : T'.toGrp ⟶ G'` with
  `IsMaximalTorus i` and `IsMaximalTorus i'`
  ([`Torus.Maximal`](../Torus/Maximal.md)): each is a closed torus that
  factors through no strictly larger closed torus;
- a homomorphism `φ : G ⟶ G'` with `IsCentralIsogeny φ`, the published
  predicate from [`CentralIsogeny.Basic`](Basic.md): the underlying morphism
  of schemes is finite, flat, surjective and locally of finite presentation,
  and the full scheme-theoretic kernel of `φ` is central in `G`;
- a homomorphism `t : T ⟶ T'` of commutative group schemes with
  `i ≫ φ = CommGroupScheme.groupHom t ≫ i'`. So `φ` maps `T` into `T'`, and
  `t` is the restriction of `φ`;
- root index types `J J' : Type u` and Mathlib integral root data
  `P : RootDatum J (characterLattice T) (cocharacterLattice T)` and
  `P' : RootDatum J' (characterLattice T') (cocharacterLattice T')` with
  `IsRootDatumOf i P` and `IsRootDatumOf i' P'`. The lattices are the actual
  `X^*(T) = Hom(T, 𝔾_m)` and `X_*(T) = Hom(𝔾_m, T)`
  ([`Torus.Lattice`](../Torus/Lattice.md)). The published predicate
  `IsRootDatumOf` from [`Reductive.RootDatum`](../Reductive/RootDatum.md)
  says that the pairing of the datum is the actual `latticePairing`,
  `⟨χ, ν⟩ = ν ≫ χ ∈ End(𝔾_m) = ℤ`, that the range of its roots is the set
  `roots i` of the group, and that each reflection is induced by a `k`-point
  normalizing the torus.

`IsRootDatumOf` requires `IsAffineHom G.X.hom`. The statement supplies it as
`hG.isAffineHom` (and `hG'.isAffineHom`) by `haveI`, so no extra instance
argument is introduced.

## Conclusion

There is a morphism of root pairings `f : RootPairing.Hom P' P` such that

- `f.weightMap χ = t ≫ χ` for every character `χ` of `T'`. So the weight map
  `X^*(T') → X^*(T)` is pullback of characters along `t`;
- `f.coweightMap ν = ν ≫ t` for every cocharacter `ν` of `T`. So the coweight
  map `X_*(T) → X_*(T')` is pushforward of cocharacters along `t`;
- `f.weightMap` and `f.coweightMap` are injective;
- `IsIso φ ↔ Function.Bijective f.weightMap`: the isogeny `φ` is an
  isomorphism exactly when pullback of characters along `t` is bijective.

A Mathlib morphism `RootPairing.Hom P' P`
(`Mathlib/LinearAlgebra/RootSystem/Hom.lean`) consists of the weight map
`M' → M`, the coweight map `N → N'`, and a bijection `indexEquiv : J' ≃ J`.
These must satisfy three conditions:

- `weight_coweight_transpose`: the two maps are transposes for the pairings
  of `P` and `P'`;
- `root_weightMap`: the weight map sends the root `P'.root j` to
  `P.root (indexEquiv j)`;
- `coroot_coweightMap`: the coweight map sends the coroot `P.coroot j` to
  `P'.coroot (indexEquiv.symm j)`.

The existence of `f` therefore says that pulling back along `t` gives a
bijection from the roots of `G'` to the roots of `G`. It also says that
pushforward along `t` sends each coroot of `G` to the coroot of the
corresponding root of `G'`. The maps are fixed by the first two items of the
conclusion; only the existence of `indexEquiv` and the three conditions are
asserted.

## Sources and provenance

The statement is derived from published results; the Lean form is not
verbatim.

**Milne.** J. S. Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`:

- Definition 23.1, printed p.483 (PDF p.499): an injective homomorphism
  `f : X' → X` with finite cokernel is an isogeny of root data
  `R' → R` if there are a bijection `α ↔ α' : Φ ↔ Φ'` and a map
  `q : Φ → p^ℕ` with `f(α') = q(α)α` and `f^∨(α^∨) = q(α)α'^∨` for all
  `α ∈ Φ`. Milne's `X` is the character lattice and `f^∨ : X^∨ → X'^∨` is the
  transpose of `f`.
- The paragraph after it, printed p.484 (PDF p.500): "the following
  conditions on a homomorphism f: X' → X are equivalent: (a) f is injective
  with finite cokernel; (b) both f and f^∨ are injective; (c) f_ℚ is an
  isomorphism."
- Definition 23.2, printed p.484 (PDF p.500): "An isogeny f of root data is
  central if q(α) = 1 for all α ∈ Φ; it is an isomorphism if it is central
  and f is an isomorphism of ℤ-modules."
- Before Proposition 23.5, printed p.485 (PDF p.501): "An isogeny of split
  reductive groups (G, T) → (G', T') is an isogeny φ: G → G' such that
  φ(T) ⊂ T'. We write φ_T for φ|T: T → T'."
- Proposition 23.5, printed p.485 (PDF p.501): "If φ: (G,T) → (G',T') is an
  isogeny of split reductive groups, then f = X(φ_T): X(T') → X(T) is an
  isogeny of root data. … The isogeny φ is central (resp. an isomorphism) if
  and only if f is central (resp. an isomorphism)." Its proof, printed
  pp.485–486 (PDF pp.501–502), begins: "The restriction of φ to T is an
  isogeny T → T', and so f: X(T') → X(T) is injective with finite cokernel."
- Definition 6.6, printed p.126 (PDF p.142): a homomorphism is an isogeny
  if its kernel is finite and its image has finite index. For connected
  `G'`, this means finite kernel and surjective.

**Translation.**

- *The setting.* `IsCentralIsogeny φ` makes `φ` finite and surjective, so it
  is an isogeny in Milne's sense, and its kernel is central. Splitness of the
  maximal tori `T`, `T'` makes `(G, T)` and `(G', T')` split reductive groups.
  The equation `i ≫ φ = groupHom t ≫ i'` is `φ(T) ⊂ T'` with `φ_T = t`.
- *The maps.* Milne's `f = X(φ_T)` sends `χ'` to `χ' ∘ φ_T`, which is
  `t ≫ χ'`: this is `f.weightMap`. Under the actual pairing
  `⟨χ, ν⟩ = ν ≫ χ` one has `⟨t ≫ χ', ν⟩ = ⟨χ', ν ≫ t⟩`. So the transpose
  `f^∨` is `ν ↦ ν ≫ t` on cocharacters: this is `f.coweightMap`. The
  identity is the condition `weight_coweight_transpose`, because
  `IsRootDatumOf` fixes both pairings to be `latticePairing`.
- *The roots.* By Proposition 23.5, `f` is an isogeny of root data. As `φ` is
  central, `f` is central, so `q(α) = 1`. Then `f(α') = α` and
  `f^∨(α^∨) = α'^∨` for the bijection `α ↔ α'`. Since `P.root` and `P'.root`
  are embeddings with ranges `roots i` and `roots i'`, the bijection
  `α ↔ α'` gives `indexEquiv : J' ≃ J`. The two equations are
  `root_weightMap` and `coroot_coweightMap`.
- *The coroots.* For this, the coroots of the supplied `P` must be the
  coroots of the group. `IsRootDatumOf` does not name coroots, but it fixes
  the pairing, the roots, and that each reflection of `P` is the action of a
  point normalizing the torus. Such an action lies in the finite Weyl group.
  A reflection of `P` fixes a hyperplane pointwise and sends its root `α`
  to `-α`. A Weyl-invariant positive form shows that such an element is the
  group's reflection in `α`. Perfectness of the pairing then determines the
  coroot from that reflection. The independent review of
  [`SimplyConnected.SplitCriterionStatement`](../SimplyConnected/SplitCriterionStatement.md)
  accepted this argument. The same identification is the uniqueness of the
  root datum of a split maximal torus, `RootDatumUniquenessStatement` in
  [`Reductive.RootDatumStatement`](../Reductive/RootDatumStatement.md)
  (not proved).
- *Injectivity.* `f` is injective with finite cokernel, so by the
  equivalence (a) ⇔ (b) both `f` and `f^∨` are injective.
- *The isomorphism clause.* For the central isogeny `φ`, Proposition 23.5 and
  Definition 23.2 say that `φ` is an isomorphism exactly when `f` is an
  isomorphism of `ℤ`-modules. That is `IsIso φ ↔ Bijective f.weightMap`. The
  last paragraph of Milne's proof gives the reason: the kernel of a central
  isogeny lies in `T`, so `φ` is an isomorphism exactly when `φ_T` is, and
  `φ_T` is an isomorphism exactly when `X(φ_T)` is.

Milne requires root data to be reduced (printed p.483). The roots of a split
reductive group are reduced, so this places no condition on `P` or `P'`. The
Lean statement assumes no `[Finite J]` instance and no reducedness
hypothesis.

**Errata.** The project snapshot of Milne's errata
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for printed
pp.126, 483, 484, 485 or 486. Its Chapter 23 entries start at p.488
(proof of 23.11).

## Role in the Library

This statement is an internal step towards the coroot criterion
`SplitCorootSpanSimplyConnectedStatement` (Milne, Proposition 23.29) for
`IsSimplyConnectedFieldExtensionStatement` in
[`SimplyConnected.FieldExtensionStatement`](../SimplyConnected/FieldExtensionStatement.md).
In that argument, `φ` is a central isogeny onto a split semisimple group
whose coroots span its cocharacter lattice. The coroots of the target are
then images of coweights under `f.coweightMap`, so `f.coweightMap` is
surjective. By the transpose identity `f.weightMap` is bijective, and `φ` is
an isomorphism. This module proves none of those steps.
