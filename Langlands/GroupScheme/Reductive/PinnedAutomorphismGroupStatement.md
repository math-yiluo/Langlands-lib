# Statement: the automorphism group of a pinned split reductive field group

Author: Worker 75.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.PinnedAutomorphismGroupStatement.{u}`. The Lean file only
defines the proposition. It contains no proof of it and adds no other declarations
or axioms. It imports [`Reductive.PinnedAutomorphismLift`](PinnedAutomorphismLift.md),
[`Adjoint.InnerAction`](../Adjoint/InnerAction.md) and
[`AutomorphicActionPointIso`](../AutomorphicActionPointIso.md).

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over:

- every field `k : Type u`, with no restriction on the characteristic or on
  perfectness;
- group schemes `G A : GroupScheme (Spec (CommRingCat.of k))`, with an
  `IsAffineHom G.X.hom` instance on `G`;
- a pinning `p : SplitPinning G` from [`Reductive.Pinning`](Pinning.md). It bundles
  connected reductivity of `G`, a split maximal torus `p.inclusion : p.torus ⟶ G`, a
  finite reduced root datum `p.rootDatum` on the character and cocharacter lattices
  of `p.torus` satisfying `IsRootDatumOf`, a base `p.base`, and trivializations of
  the simple-root Lie spaces. This is Conrad's pinned split group
  `(G, T, M, {X_a}_{a ∈ Δ})`;
- a homomorphism `q : G ⟶ A` with `hq : IsAdjointQuotient q` from
  [`Adjoint.Quotient`](../Adjoint/Quotient.md): `A` is adjoint, `q` is flat,
  surjective and locally of finite presentation, its kernel is the
  scheme-theoretic centre of `G`, and `q` has the group and scheme quotient
  universal properties for maps killing the centre. So `A` is `G/Z_G`.

## Conclusion

There exist group homomorphisms

- `inn : (Over.mk (𝟙 (Spec k)) ⟶ A.X) →* Aut G`, from the group `A(k)` of
  `k`-points of `A` to the group of automorphisms of `G` as a group scheme over
  `Spec k`, and
- `π : Aut G →* p.basedRootDatumAut`,

such that

1. `inn x = hq.innerAction.basePointIso x` for every `x ∈ A(k)`. Here
   `hq.innerAction` ([`Adjoint.InnerAction`](../Adjoint/InnerAction.md)) is the
   action of `A` on `G` descended from conjugation, and `basePointIso x`
   ([`AutomorphicActionPointIso`](../AutomorphicActionPointIso.md)) is the
   automorphism of `G` by which the point `x` acts. So the action of `A(k)` on `G`
   is a group homomorphism `A(k) → Aut G`;
2. `inn` is injective;
3. `π.ker = inn.range`: an automorphism maps to the identity of the based root
   datum exactly when it comes from `A(k)`;
4. `π (p.basedRootDatumAutLift θ) = θ` for every `θ ∈ p.basedRootDatumAut`.

`p.basedRootDatumAut` ([`Reductive.PinnedAutomorphismLift`](PinnedAutomorphismLift.md))
is the group of automorphisms of the root datum `p.rootDatum` whose root
permutation preserves the simple roots of `p.base`, that is, Conrad's
`Θ = Aut(R(G, T), Δ)`. `p.basedRootDatumAutLift : p.basedRootDatumAut →* Aut G` is
the Library's homomorphism sending `θ` to the automorphism of `G` that preserves
`p.torus`, acts on its characters by `θ` and carries the pinning to itself.

In `Aut G`, the product `σ * τ` is `τ ≪≫ σ` (first `τ`, then `σ`), as in Mathlib.

Together, these clauses say that
`1 → A(k) → Aut G → Aut(R(G, T), Δ) → 1` is exact, and that the pinned lift is a
homomorphic section of `π`. Clause 4 makes `π` surjective. Hence
`Aut G ≃ A(k) ⋊ Aut(R(G, T), Δ)`, with `A(k)` acting through `inn`.

The homomorphism `π` is unique. If `π'` also satisfies clauses 3 and 4, write
`σ = σ * (lift (π σ))⁻¹ * lift (π σ)`. The first factor lies in `ker π = inn.range
= ker π'`, so `π' σ = π' (lift (π σ)) = π σ`.

## Source and provenance

The statement is derived from a published result; the Lean form is not verbatim.
Source: B. Conrad, *Reductive group schemes* (2014), SGA3 summer school notes;
printed page = PDF page.

- Proposition 7.1.6, pp.243–244: "Let `(G, T, M, {X_a}_{a∈∆})` be a pinned split
  connected reductive group over a field `k`. The group `Aut(G)` is naturally an
  extension of `Aut(R(G, T), ∆)` by `(G/Z_G)(k)`, and the pinning naturally splits
  this extension as a semi-direct product."
- p.242: "The action of `G` on itself by conjugation factors through an action of
  `G/Z_G` on `G`. This identifies the adjoint quotient `G/Z_G` with a subfunctor of
  the automorphism functor `Aut_{G/k}`, so `(G/Z_G)(k)` is a subgroup of
  `Aut_{G/k}(k) = Aut(G)`. Note that this works even when `G(k) → (G/Z_G)(k)` fails
  to be surjective, and that it defines a normal subgroup of `Aut(G)`."
- p.243: "the choice of pinning defines an injective homomorphism `Θ ↪ Aut(G)` with
  image equal to the automorphism group of `(G, T, B, {X_a}_{a∈∆})`, so `Θ` is
  carried to a subgroup of `Aut(G)` that preserves `T` and `B` and maps
  isomorphically onto `Aut(G)/(G/Z_G)(k)`. We have just constructed an isomorphism of
  groups (7.1.3) `(G/Z_G)(k) ⋊ Aut(R(G, T), ∆) ≃ Aut(G)`."

**Translation.**

- *`(G/Z_G)(k)` and its action.* `A` with `q` is the adjoint quotient `G/Z_G`, and
  `A(k)` is the group of sections of `A` over `Spec k`. Conrad's action of `G/Z_G`
  on `G` is the one induced by conjugation. In the Library it is
  `hq.innerAction`, whose formula on lifted points is
  `innerAction(q(h), g) = h g h⁻¹`. It is defined on all points of `A`, including
  those that do not lift to `G(k)`, as in Conrad's remark. Conrad's statement that
  `(G/Z_G)(k)` "is a subgroup of `Aut(G)`" is clauses 1 and 2. Its normality is
  part of clause 3, because a kernel is normal.
- *The extension.* "`Aut(G)` is an extension of `Θ` by `(G/Z_G)(k)`" means there is
  a surjective homomorphism `Aut(G) → Θ` with kernel `(G/Z_G)(k)`. This is `π` with
  clauses 3 and 4.
- *The splitting by the pinning.* Conrad's section `Θ ↪ Aut(G)` sends `θ` to the
  unique automorphism preserving `(T, B, {X_a})` that induces `θ` (Theorem 6.1.17).
  The Library's `p.basedRootDatumAutLift` is this section. It preserves `T` and
  the pinning, and it induces `θ` on the character lattice
  (`basedRootDatumAutLift_square`, `basedRootDatumAutTorusLift_character`,
  `basedRootDatumAutLift_rootVector`). Preserving `B` is implicit: `B` is
  determined by `T` and the positive system of `Δ`. Clause 4 says that this lift
  is a section of `π`.
- *Naturality.* In Conrad, the map `Aut(G) → Θ` is the canonical action of `Aut(G)`
  on the based root datum (Remark 7.1.2). The statement asserts the existence of
  `π`; it is unique, as shown above. The statement does not describe `π` through
  the canonical based root datum of Remark 7.1.2.
- *Based root datum.* Conrad's `Aut(R(G, T), ∆)` consists of the automorphisms of
  the root datum `R(G, T)` that preserve `∆`. In `p.basedRootDatumAut`, an element
  is a `RootPairing.Aut` of `p.rootDatum`, with weight, coweight and root-index
  equivalences, whose root-index equivalence preserves the simple roots. The root
  datum is reduced, so the root index is in bijection with the roots.
- *Fields.* Conrad states the result for `Aut(G)` over the ground field `k`; the
  remark that it is compatible with extension of the ground field is not stated.
  Here `Aut G` is the group of automorphisms of `G` as a group scheme over
  `Spec k`.

## Scope

No semisimplicity is assumed. If `G` is a split torus, its adjoint quotient is
trivial, `A(k)` is trivial, and the statement says that `π` is an isomorphism from
`Aut G` onto the automorphism group of the root datum, which has no roots. No
perfectness or characteristic restriction is imposed. The statement does not
assume that `q` or a pinning exists; it is about given ones.

## Not stated

The statement does not describe `π σ` for a given `σ`, for example as the
automorphism of `R(G, T)` induced by `σ` when `σ` preserves `T` and `B`. That
description needs, besides these clauses, the fact that an automorphism
preserving `T` and `B` and inducing the identity of `R(G, T)` comes from
`(T/Z_G)(k)` (Conrad, p.243). The statement also does not state that the
splitting depends on the pinning. It does not state Theorem 7.1.9, the
representability of the automorphism functor `Aut_{G/k}` or the exact sequence of
`k`-group schemes `1 → G/Z_G → Aut_{G/k} → Out_{G/k} → 1`. It does not treat
non-split groups, where the extension need not split (Conrad, Example 7.1.12).

## Role in the Library

This is a statement for the program of reductive group schemes over fields. A
separate proof task will prove it. The intended route follows Conrad pp.242–243:
conjugacy of split maximal tori and Borel subgroups containing them
(Proposition 6.2.11(2)), simple transitivity of `(T/Z_G)(k)` on pinnings, and the
Isomorphism Theorem with pinnings (Theorem 6.1.17; Library
[`PinnedIsomorphismStatement`](PinnedIsomorphismStatement.md) and
[`PinnedRigidityStatement`](PinnedRigidityStatement.md)).
