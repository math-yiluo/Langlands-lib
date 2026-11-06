# Statement: rigidity of actual pinned split reductive groups

Author: Worker 1416.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.PinnedAutomorphismRigidityStatement.{u}`. The Lean
file only defines the proposition. It contains no proof of it and adds no
other declarations or axioms. It imports only
[`Reductive.Pinning`](Pinning.md).

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over:

- every field `k : Type u`, with no restriction on the characteristic or
  on perfectness;
- a group scheme `G : GroupScheme (Spec (CommRingCat.of k))` with an
  `IsAffineHom G.X.hom` instance;
- a pinning `p : SplitPinning G` from [`Reductive.Pinning`](Pinning.md).
  It bundles actual connected reductivity of `G`, a split maximal torus
  `p.inclusion : p.torus ⟶ G`, a finite reduced root datum `p.rootDatum`
  on the actual character and cocharacter lattices of `p.torus` that
  satisfies `IsRootDatumOf`, a base `p.base`, and linear trivializations
  `k ≃ weightSpace p.inclusion (p.rootDatum.root a)` of the actual
  simple-root Lie spaces. The chosen simple-root vector
  `p.pinning.rootVector a` is the image of `1`;
- an automorphism `σ : G ≅ G` of group schemes over `Spec k`.

The two hypotheses on `σ` are:

- `p.inclusion ≫ σ.hom = p.inclusion`: `σ` restricts to the identity of
  the pinned torus;
- for every `a` in the support of `p.base`,
  `Lie.targetMapLinear σ.hom (CommRingCat.of k) (p.pinning.rootVector a)
  = p.pinning.rootVector a`. Here `Lie.targetMapLinear` is the published
  linear differential on the actual dual-number identity kernel
  ([`Lie.KernelTargetMaps`](../Lie/KernelTargetMaps.md)). So the
  differential of `σ` fixes every chosen simple-root vector.

## Conclusion

`σ = Iso.refl G`: the automorphism is the identity.

There is no semisimplicity hypothesis. Groups with a central torus and
groups with no roots are included; in the latter case the second
hypothesis is empty and the statement says that an automorphism fixing a
maximal torus pointwise is the identity.

## Source and provenance

The statement is derived from published results; the Lean form is not
verbatim. Source: B. Conrad, *Reductive group schemes* (2014), SGA3
summer school notes; printed page = PDF page.

- Proposition 6.1.13(2), p.194: for an isogeny `f` compatible with the
  splittings, a pinning `{X'_{a'}}` of the source and the pinning of the
  target given by `X_{d(a')} = f_{a'}(X'_{a'} ⊗ q(a'))`, "f is uniquely
  determined by R(f) and the pinnings". Its proof (pp.194–195) determines
  `f` on the simple root groups, then on all root groups via the Weyl
  group, then on the open cell, and concludes by schematic density.
- Corollary 6.1.15, p.195: the functor from pinned split reductive groups
  with pinning-compatible isogenies to root data is faithful; Conrad
  states that this "is immediate from Proposition 6.1.13(2)".
- Definition 6.1.1, p.186: a pinning is a base `∆` with trivializing
  sections `X_a ∈ g_a(S)` for `a ∈ ∆`.
- Lemma 6.1.4, p.188: `f_{a'}` is the unique isomorphism with
  `f(exp_{a'}(X')) = exp_{d(a')}(f_{a'}(X'^{⊗ q(a')}))`.
- Theorem 4.1.4, p.110: `exp_a : W(g_a) → G` induces the canonical
  inclusion `g_a ⊂ g` on Lie algebras.

**Translation.** Take `S = Spec k`, the split reductive group `(G, T, M)`
with `T = p.torus` and `M` its actual character lattice, and the pinning
`{X_a} = {p.pinning.rootVector a}`. Both `σ` and the identity of `G` are
isomorphisms `(G, T, M) → (G, T, M)` compatible with the splittings,
since both map `T` to `T`.

- *Equal root-datum morphisms.* Since `σ` restricts to the identity of
  `T`, the map it induces on characters is the identity, so `R(σ)` is the
  identity morphism of the root datum, with `d = id` and `q = 1`. This is
  `R(id_G)`.
- *Equal pinnings.* For an isomorphism `q(a') = 1`, so `f_{a'}` is the
  linear map `g_{a'} → g_{d(a')}` with `f ∘ exp_{a'} = exp_{d(a')} ∘ f_{a'}`.
  Differentiating and using Theorem 4.1.4 shows that `f_{a'}` is the
  restriction of the differential of `f`. Hence the target pinning
  attached by Proposition 6.1.13(2) to `σ` and `{X_a}` is
  `{dσ(X_a)} = {X_a}` by the second hypothesis. The pinning attached to
  the identity is also `{X_a}`.
- *Conclusion.* Proposition 6.1.13(2) says that `R(f)` and the two pinnings
  determine `f`, so `σ = id_G`.

Conrad's sentence after Proposition 6.1.13(2) ("if G is semisimple then an
automorphism of `(G, T, M, {X_a})` whose effect on `g` is the identity on
each `X_a` must be the identity") assumes semisimplicity because there the
automorphism is not assumed to be the identity on `T`. Here it is, which
fixes `R(σ)` directly, so no semisimplicity is needed.

Conrad works with reductive group schemes over a non-empty scheme. Over a
field these are smooth affine groups with connected reductive fibre, which
is the published predicate `IsConnectedReductive`. The split maximal
torus and the actual character lattice give Conrad's split triple; over a
field the simple root spaces are lines, and the pinning trivializes them.

## Role in the Library

This statement is planned as the rigidity hypothesis of
`PinnedIsomorphism.Prerequisites` in the module
`Reductive.PinnedIsomorphismReduction`, which is submitted separately and
is not yet in the Library. There it gives the uniqueness part of the
published [`PinnedIsomorphismStatement`](PinnedIsomorphismStatement.md).
This module does not prove it.
