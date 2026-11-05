# Statement: the Isomorphism Theorem for split reductive groups with a common maximal torus

Authors: Worker 277 (draft), Worker 1388.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.SplitCommonTorusIsomorphismStatement`. The Lean file
only defines the proposition. It contains no proof of it, and it adds no
other definitions, theorems or axioms. The module imports only
[`Reductive.RootDatum`](RootDatum.md).

It is the existence part of the Isomorphism Theorem for split reductive
groups (Milne, Theorem 23.25 in its "isomorphism" form, and Remark 23.26), in
the special case where the two groups share the same split maximal torus and
the isomorphism of root data is the identity of the character lattice.

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over:

- every field `k : Type u`. The field may be imperfect, of positive
  characteristic, and need not be separably closed;
- group schemes `G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))` with proofs
  `hG₁ : IsConnectedReductive G₁` and `hG₂ : IsConnectedReductive G₂`. This
  published predicate from [`Reductive.Basic`](Basic.md) says that the group
  is smooth, affine and connected over `k`, and that its base change to an
  algebraic closure has trivial unipotent radical;
- one commutative group scheme `T` with `IsSplitTorus T.toGrp`, that is, `T`
  is isomorphic to `𝔾_m^I` for a finite index type `I`
  ([`Torus.Split`](../Torus/Split.md));
- homomorphisms `i₁ : T.toGrp ⟶ G₁` and `i₂ : T.toGrp ⟶ G₂` with
  `IsMaximalTorus i₁` and `IsMaximalTorus i₂`
  ([`Torus.Maximal`](../Torus/Maximal.md)): each is a closed subgroup whose
  source is a torus, and it factors through no strictly larger closed torus
  of the group. So `T` is a split maximal torus of both groups;
- root index types `J₁ J₂ : Type u` and Mathlib integral root data
  `P₁ P₂ : RootDatum _ (characterLattice T) (cocharacterLattice T)`, indexed
  by `J₁` and `J₂`, with `IsRootDatumOf i₁ P₁` and `IsRootDatumOf i₂ P₂`.
  Both data live on the actual lattices `X^*(T) = Hom(T, 𝔾_m)` and
  `X_*(T) = Hom(𝔾_m, T)` of homomorphisms of commutative group schemes over
  `Spec k` ([`Torus.Lattice`](../Torus/Lattice.md)). The published predicate
  `IsRootDatumOf` from [`Reductive.RootDatum`](RootDatum.md) says three
  things: the pairing of the datum is the actual `latticePairing T`,
  `⟨χ, ν⟩ = gmEndEquiv k (ν ≫ χ)`, the integer of the endomorphism `ν ≫ χ`
  of `𝔾_m`; the range of its roots is the set `roots i` of the group (the
  nonzero characters of `T` with a nonzero weight space in `Lie(G)`); and
  each reflection `P.reflection α` is the action `χ ↦ σ⁻¹ ≫ χ` of some
  `k`-point of the group normalizing the torus through an automorphism `σ`
  of `T`;
- a bijection `e : J₁ ≃ J₂` with `P₂.root ∘ e = P₁.root` and
  `P₂.coroot ∘ e = P₁.coroot`. So `G₁` and `G₂` have the same roots in
  `X^*(T)`, and each root has the same coroot in `X_*(T)` for both groups.

`IsRootDatumOf` requires `IsAffineHom G.X.hom`. The statement supplies it as
`hG₁.isAffineHom` and `hG₂.isAffineHom` by `haveI`, as the published
`RootDatumUniquenessStatement` does, so no extra instance argument is
introduced.

The statement assumes neither `[Finite J₁]` nor reducedness of `P₁` or `P₂`.
This adds no generality beyond the source. `P.root` is injective, so `J₁` is
in bijection with `roots i₁`. Milne's root datum `R(G, T)` of a split
reductive group is reduced and has a finite set of roots (Theorem 21.11,
printed pp.428–430, PDF pp.444–446, and Corollary 21.12, printed p.430;
recorded in the Library as `RootDatumExistenceStatement`). Any datum
satisfying `IsRootDatumOf` has the actual roots. Its coroots are also the
actual coroots: a reflection of `X^*(T)` with vector `α` lying in the finite
Weyl group is unique, and with it the coroot of 21.11(e). The Library
records this as `RootDatumUniquenessStatement` in
[`Reductive.RootDatumStatement`](RootDatumStatement.md). Neither statement
is proved in this module. So `P₁` and `P₂` are Milne's root data `R(G₁, T)`
and `R(G₂, T)` up to reindexing.

## Conclusion

There is an isomorphism `ψ : G₁ ≅ G₂` in `GroupScheme (Spec k)`, that is,
an isomorphism of group schemes over `Spec k`, with `i₁ ≫ ψ.hom = i₂`. So
`ψ` maps the torus `T` of `G₁` onto the torus `T` of `G₂` by the identity of
`T`.

## Sources and provenance

The statement is derived from published results; the Lean form is not
verbatim. Source: J. S. Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups` (printed page = PDF page − 16).

- Theorem 23.25 (Full Isogeny Theorem), printed pp.492–493
  (PDF pp.508–509): "Let φ: (G,T) → (G',T') be an isogeny of split reductive
  groups over the field k; then φ defines an isogeny f = X(φ|T):
  R(G',T') → R(G,T) of root data, and every isogeny of root data arises in
  this way from an isogeny of split reductive groups; moreover, φ is uniquely
  determined by f up to an inner automorphism defined by an element of
  (T'/Z')(k). This statement also holds with "isogeny" replaced by "central
  isogeny", "Frobenius isogeny", or "isomorphism"." Its proof combines 23.5,
  23.6, 23.7 and the Isogeny Theorem 23.9.
- Remark 23.26, printed p.493 (PDF p.509): "In particular, an isomorphism φ
  of split reductive groups defines an isomorphism f of root data, and every
  isomorphism of root data f arises from a φ, unique up to the inner
  automorphism defined by an element of (T'/Z')(k). This statement is called
  the isomorphism theorem."
- Definition 19.22, printed p.402 (PDF p.418): a split reductive group over
  `k` is a pair `(G, T)` of a reductive group `G` over `k` and a split
  maximal torus `T` in `G`; a homomorphism `(G, T) → (G', T')` is a
  homomorphism `φ : G → G'` with `φ(T) ⊂ T'`. By 6.46, printed p.135
  (PDF p.151), recalled on printed p.400, a reductive group is smooth and
  connected with trivial geometric unipotent radical.
- Before Proposition 23.5, printed p.485 (PDF p.501): an isogeny of split
  reductive groups `(G, T) → (G', T')` is an isogeny `φ : G → G'` with
  `φ(T) ⊂ T'`, and `φ_T = φ|T`.
- Definition 23.1, printed p.483 (PDF p.499): an isogeny of root data
  `R' → R` is an injective homomorphism `f : X' → X` with finite cokernel and
  a bijection `α ↔ α'` of roots and a map `q : Φ → p^ℕ` with
  `f(α') = q(α)α` and `f^∨(α^∨) = q(α)α'^∨`. Milne requires root data to be
  reduced (same page).
- Definition 23.2, printed p.484 (PDF p.500): an isogeny of root data is an
  isomorphism if it is central (`q = 1`) and `f` is an isomorphism of
  `ℤ`-modules. "Thus an isomorphism f: X' → X of ℤ-modules is an isomorphism
  of root data if and only if there exists a one-to-one correspondence
  α ↔ α': Φ ↔ Φ' such that f(α') = α and f^∨(α^∨) = α'^∨ for all α ∈ Φ."
- Theorem 12.9(a), printed p.233 (PDF p.249): `M ↦ D(M)` is a contravariant
  equivalence from finitely generated commutative groups to diagonalizable
  algebraic groups, with quasi-inverse `G ↦ X(G)`.

**Translation.** The statement is the existence part of the isomorphism
case of Theorem 23.25 (Remark 23.26) for `(G, T) = (G₁, T)`,
`(G', T') = (G₂, T)` and `f` the identity of `X^*(T)`.

- *The setting.* `IsConnectedReductive` matches 6.46, and the split maximal
  tori `i₁`, `i₂` make `(G₁, T)` and `(G₂, T)` split reductive groups in the
  sense of Definition 19.22, both with the same torus `T`.
- *The isomorphism of root data.* For `f = id` the transpose `f^∨` is the
  identity of `X_*(T)`, because both data use the same `latticePairing`. By
  Definition 23.2, `f = id` is an isomorphism of root data
  `R(G₂, T) → R(G₁, T)` exactly when there is a bijection `α ↔ α'` from the
  roots of `G₁` to the roots of `G₂` with `α' = α` and `α^∨ = α'^∨`: the two
  groups have the same roots, and each root has the same coroot in both
  groups. Since `P₁.root` and `P₂.root` are embeddings with ranges `roots i₁`
  and `roots i₂`, and their coroots are the actual coroots (previous
  section), this is exactly the hypothesis on `e`.
- *The conclusion.* The isomorphism case of Theorem 23.25 gives an
  isomorphism `φ : G₁ → G₂` with `φ(T) ⊂ T` and `X(φ_T) = f = id`. A
  homomorphism of split tori is determined by its pullback on characters
  (Theorem 12.9(a), since a split torus is diagonalizable; in the Library,
  `IsSplitTorus.hom_ext_of_characters` in
  [`Torus.CharacterIsomorphism`](../Torus/CharacterIsomorphism.md)), so `φ_T`
  is the identity of `T`. That is `i₁ ≫ φ = i₂`, with `ψ.hom = φ`.
- *Omitted parts.* The uniqueness of `φ` up to the inner automorphism by an
  element of `(T/Z)(k)` and the converse direction (an isomorphism of split
  reductive groups defines an isomorphism of root data) are not included.

**Proof route.** Milne derives the Isomorphism Theorem from the Isogeny
Theorem 23.9, whose proof (printed pp.487–492, PDF pp.503–508) follows
Steinberg (1999), rewritten for split groups over an arbitrary field. A proof
of this statement therefore needs that argument (23.10–23.24) in the case
where the torus map is the identity of `T`. The case of semisimple rank one
(23.14) extends the torus map to each `G_α → G'_α` for `α` in a base (23.16).
The subgroup of `G₁ × G₂` generated by the graphs of these maps projects
isomorphically onto `G₁` (23.17–23.24). Composing the inverse projection with
the second projection gives a homomorphism extending the identity of `T`.
It is an isogeny by 23.10, and an isomorphism by 23.5 because `f = id` is an
isomorphism of root data. None of these steps is in the Library yet; only the
torus step (`IsSplitTorus.hom_ext_of_characters`) is published.

**Errata.** The official errata snapshot
(`milne-2017-algebraic-groups-errata-2026-11-02`), read in full, has no
entry for printed pp.135, 233, 400, 402, 428–430, 483, 484, 485, 492 or 493. Its
Chapter 23 entries are for p.488 and pp.494 onwards; the p.488 entry (proof
of 23.11, inside the proof route above) changes `U_{α₂}` to `U_{α₂}(k)`. Its
Chapter 21 entries for p.440 (proof of Theorem 21.51 rewritten; 21.51 is used
in the proof of 23.24, printed p.492) and p.449 concern proofs, not the
statements used here. The p.449 entry says "In the proof of Proposition 21.11,
replace the appeal to 21.67 with a direct argument". Printed p.449 (PDF
p.465) holds the proof of Proposition 21.77, which appeals to
Proposition 21.67. Theorem 21.11 is on printed pp.428–430. So the entry
concerns the proof of 21.77, not Theorem 21.11.

## Role in the Library

This statement is an internal step towards the existence part of the central
Isogeny Theorem, `SplitCentralIsogenyExistenceStatement` in
[`Reductive.SplitClassificationStatement`](SplitClassificationStatement.md).
There, a central isogeny of root data is first realised by a quotient of the
source group by a central subgroup of its torus, which has the target's
torus. The quotient and the target group then have a common split maximal
torus and matching roots and coroots, and this statement identifies them.
This module proves none of those steps.
