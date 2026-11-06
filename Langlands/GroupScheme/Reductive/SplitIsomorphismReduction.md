# Reduction of the Isomorphism Theorem to semisimple rank at most one

Author: Worker 712.

This internal assembly proves one lemma and a conditional result, and bundles
the hypotheses of the conditional result into one proposition.

- `Langlands.GroupScheme.IsRootDatumOf.coroot_eq_of_comp_of_mono_of_finite_weylImage`
  is a theorem comparing coroots in a group and in a subgroup.
- `Langlands.GroupScheme.splitCommonTorusIsomorphism_of_leviGluing` is the
  conditional theorem described below.
- `Langlands.GroupScheme.SplitCommonTorusIsomorphism.Prerequisites` is the
  proposition

  ```text
  RootDatumExistenceStatement.{u} ∧ DynamicCentralizerReductiveStatement.{u} ∧
    SplitRankOneCommonTorusIsomorphismStatement.{u} ∧
    SplitCommonTorusLeviGluingStatement.{u}
  ```

  and
  `SplitCommonTorusIsomorphism.splitCommonTorusIsomorphismStatement_of_prerequisites`
  derives the target from it by applying
  `splitCommonTorusIsomorphism_of_leviGluing` to the four components.

The conditional result shows that the published
`SplitCommonTorusIsomorphismStatement`
([`SplitIsomorphismStatement`](SplitIsomorphismStatement.md); Milne,
Theorem 23.25 in its isomorphism form and Remark 23.26, for two groups with a
common split maximal torus and the identity of the character lattice) follows
from four statements, taken as hypotheses in this order:

- `RootDatumExistenceStatement` ([`RootDatumStatement`](RootDatumStatement.md)):
  every split maximal torus of a connected reductive group has a root datum;
- `DynamicCentralizerReductiveStatement`
  ([`Dynamic.CentralizerReductiveStatement`](../Dynamic/CentralizerReductiveStatement.md)):
  every closed representative of the centralizer of a cocharacter of a
  connected reductive group is connected reductive;
- `SplitRankOneCommonTorusIsomorphismStatement`
  ([`SplitRankOneIsomorphismStatement`](SplitRankOneIsomorphismStatement.md)):
  the target statement when any two roots are linearly dependent (semisimple
  rank at most one);
- `SplitCommonTorusLeviGluingStatement`
  ([`SplitLeviGluingStatement`](SplitLeviGluingStatement.md)): the target
  statement follows once the centralizers of cocharacters of semisimple rank
  at most one are isomorphic over `T`.

The module proves none of these four statements. It also uses
`DynamicCentralizerRootsStatement`
([`Dynamic.CentralizerRootsStatement`](../Dynamic/CentralizerRootsStatement.md)):
the roots of a centralizer `Z_G(ν)`, for a cocharacter `ν` of a split maximal
torus `T`, are the roots `α` of `G` with `⟨α, ν⟩ = 0`. This one is not a
hypothesis: the module imports its proof `dynamicCentralizerRoots`
([`Dynamic.CentralizerRootsProof`](../Dynamic/CentralizerRootsProof.md)),
which is submitted together with this module. The conclusion is the
unchanged target statement, with every binder and the full conclusion. The
route follows Milne's passage from semisimple rank one to the general case
(23.16–23.18), with centralizers of cocharacters in place of the subgroups
`G_α`; it is internal and adds no claim from the literature.

## The coroot lemma

`IsRootDatumOf.coroot_eq_of_comp_of_mono_of_finite_weylImage` works over a field `k`
with group schemes `G` and `Z` over `Spec k`, both with affine structure
morphisms, a commutative group scheme `T`, and homomorphisms
`i : T ⟶ G`, `t : T ⟶ Z`, `z : Z ⟶ G` with `t ≫ z = i`. It assumes that the
underlying morphisms of `i` and `t` are monomorphisms, that the full
normalizer image `weylImage i` (the group of automorphisms of `X^*(T)` induced
by the `k`-points of `G` normalizing `T`) is finite, and that `P` and `Q` are
root data with `IsRootDatumOf i P` and `IsRootDatumOf t Q`. If
`P.root j = Q.root j'`, then `P.coroot j = Q.coroot j'`.

Proof. By `IsRootDatumOf`, the reflection `P.reflection j` is the action of a
normalizing `k`-point `n` of `G`, and `Q.reflection j'` is the action of a
normalizing `k`-point `m` of `Z`. The image of `m` in `G`,
`normalizerPointsMap t z i htz m`, normalizes `i` and acts on the characters
in the same way (`weylAction_normalizerPointsMap` in
[`Rational.RootKernelTorus`](../Rational/RootKernelTorus.md)). So both
reflections lie in the finite group `weylImage i`, and their product has
finite order. Both reflections send `x` to `x − f(x) α` and `x − g(x) α` with
`α = P.root j`, `f = ⟨·, P.coroot j⟩` and `g = ⟨·, Q.coroot j'⟩`, and
`f(α) = g(α) = 2` because both data use the actual lattice pairing. By
`Langlands.LinearAlgebra.eq_functional_of_finiteOrder_reflections`
([`RootDatumCorootComparison`](RootDatumCorootComparison.md)) `f = g`, and
perfectness of the pairing gives `P.coroot j = Q.coroot j'`. This is the proof
of the published `IsRootDatumOf.coroot_eq_of_finite_weylImage` (same module),
with the second reflection transported from the subgroup `Z`.

## The reduction

Let the data of the target be given: `G₁`, `G₂`, the split torus `T`, maximal
tori `i₁`, `i₂`, root data `P₁`, `P₂` and `e : J₁ ≃ J₂` matching roots and
coroots. Apply `SplitCommonTorusLeviGluingStatement` to the same data. It
remains to prove its Levi hypothesis. So let `ν` be a cocharacter of `T` such
that any two roots of `G₁` orthogonal to `ν` are linearly dependent, let
`z₁ : Z₁ ⟶ G₁` and `z₂ : Z₂ ⟶ G₂` be closed subgroups representing the
centralizers of `ν ≫ i₁` and `ν ≫ i₂`, and let `t₁`, `t₂` satisfy
`t₁ ≫ z₁ = i₁` and `t₂ ≫ z₂ = i₂`.

1. **The centralizers.** `DynamicCentralizerReductiveStatement`, applied to
   the cocharacter `CommGroupScheme.groupHom ν ≫ iⱼ`, shows that `Z₁` and `Z₂`
   are connected reductive. `IsMaximalTorus.of_comp`
   ([`Torus.MaximalTransport`](../Torus/MaximalTransport.md)) shows that `t₁`
   and `t₂` are maximal tori, since `t₁ ≫ z₁ = i₁` is maximal and `z₁` is a
   closed subgroup (similarly for `t₂`).
2. **Finiteness.** The published `splitTorusWeylImageFinite`
   ([`Torus.WeylImageFinite`](../Torus/WeylImageFinite.md)) shows that
   `weylImage i₁` and `weylImage i₂` are finite. Its instance hypotheses come
   from `hG₁` and `hG₂` (affine and smooth, hence locally of finite type), and
   `i₁`, `i₂`, `t₁`, `t₂` are closed immersions, hence monomorphisms.
3. **Root data of the centralizers.** `RootDatumExistenceStatement` gives
   root data `Q₁` of `t₁` and `Q₂` of `t₂`, indexed by `K₁` and `K₂`.
4. **Common roots.** `roots i₁ = range P₁.root = range (P₂.root ∘ e) =
   range P₂.root = roots i₂`, since `e` is surjective. By
   `dynamicCentralizerRoots`, `roots t₁` and `roots t₂` are the roots
   of `i₁` and of `i₂` orthogonal to `ν`, so `roots t₁ = roots t₂`.
5. **The reindexing.** `e' : K₁ ≃ K₂` is the composite of
   `Equiv.ofInjective Q₁.root`, the equality of ranges
   `range Q₁.root = roots t₁ = roots t₂ = range Q₂.root`, and the inverse of
   `Equiv.ofInjective Q₂.root`, as in the published
   `IsRootDatumOf.rootIndexEquiv`. Then `Q₂.root (e' j) = Q₁.root j`.
6. **Coroots.** For `j : K₁`, the root `Q₁.root j` lies in `roots t₁`, hence
   in `roots i₁` (step 4), so it is `P₁.root j₁` for some `j₁`. The coroot
   lemma for `i₁ = t₁ ≫ z₁` gives `P₁.coroot j₁ = Q₁.coroot j`. Also
   `P₂.root (e j₁) = P₁.root j₁ = Q₁.root j = Q₂.root (e' j)`, so the coroot
   lemma for `i₂ = t₂ ≫ z₂` gives `P₂.coroot (e j₁) = Q₂.coroot (e' j)`. With
   `P₂.coroot (e j₁) = P₁.coroot j₁` (hypothesis on `e`), this is
   `Q₂.coroot (e' j) = Q₁.coroot j`.
7. **Rank at most one.** By step 4, two roots `α`, `β` of `t₁` are roots of
   `i₁` orthogonal to `ν`, so they are linearly dependent by the hypothesis on
   `ν`.
8. **Conclusion.** `SplitRankOneCommonTorusIsomorphismStatement`, applied to
   `Z₁`, `Z₂`, `t₁`, `t₂`, `Q₁`, `Q₂` and `e'`, gives `φ : Z₁ ≅ Z₂` with
   `t₁ ≫ φ.hom = t₂`, which is the Levi hypothesis.

The declarations have universe parameters `u` (and `v`, `w` for the index
types of the coroot lemma) and use only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

The coroot helper's name distinguishes its two-monomorphism interface from
`IsRootDatumOf.coroot_eq_of_comp_of_finite_weylImage` in
[`RootDatumSubgroupCoroots`](RootDatumSubgroupCoroots.md), which requires only
the ambient inclusion to be a monomorphism and orders its arguments differently.
Both statements retain their original hypotheses.
