# Étale equivariant-site comparison with smooth analytic `G`-sheaves

Author: Worker 16.

## Source

Vladimir Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(1995–1996 unfinished manuscript), [Theorem 1.4.2, pp. 8–10](https://www.wisdom.weizmann.ac.il/~vova/Equish_1996.pdf#page=8),
printed and PDF pagination. Registered literature ID
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
folder SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
PDF SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The **étale** part of Theorem 1.4.2 says that inverse image along
`b : X → X(G)` gives an equivalence from sheaves on `X(G)_ét` to
`T_G(X_ét)`, the category of étale `G`-sheaves on `X`. The site and
inverse image are described in §1.2, p. 3; the induced spaces `U_{G/N}`
used in the proof are Construction 1.1.2, p. 2, with stalks computed over
them in §1.3, p. 6. Definition 1.4.1, pp. 7–8,
and the paragraph after it describe smoothness, in the étale case by
the local open-stabilizer criterion on distinguished étale objects.
The proof first establishes that `b^*E` is a `G`-sheaf (B.1), uses
`F ↦ (b_*F)^G`, with value `F(V)^G` at `V(G)`, as inverse (B.2), and
compares `E` with `(b_*b^*E)^G` (B.3, pp. 9–10).

## Model and scope

`X : GSpace.{u,v,v} K G` includes Hausdorffness of `X` and continuity
of the analytic action `X.obj.ρAut`; `G : Type z` is a topological group.
The field `K : Type u` is complete and ultrametric, and automorphisms
are over the fixed field `K`. The source allows automorphisms of the
base field (§1.1, pp. 1–2); this statement does not. The equivariant
site has the Library's topology on étale morphisms of `G`-spaces over
`X`; on the other side `EtaleGSheaf` uses the twisted étale site and
`distinguishedLiftSystem`. The twisted site is the Library model of
the action on ordinary étale sheaves. No identification with a separate
presentation of that action or with a site restricted to globally
Hausdorff ordinary test spaces is asserted.

This is the fixed-coefficient **module** version of the equivalence,
not a statement about arbitrary sheaves of sets or an equivalence of
set-valued topoi. Write `s = max u (v + 1) z uL`; the coefficient ring
`R : Type s` is commutative and both sides use `ModuleCat.{s} R`.
An integer coefficient ring (lifted to the stated universe) is the
abelian-sheaf case. The universe includes `z` for the comma-category
colimits in the published construction of `b^*`.

There is one explicit geometric input:
`hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)`. It supplies
for every cospan in `Ét(X(G))` a commutative square whose underlying
square in `Ét(X)` is a pullback. The published comparison functors use
it to prove continuity of the forgetful functor. It does not assert any
smoothness or equivalence of sheaf categories, and is not proved here.
There is no compactness premise on `X` or `G`. No quasi-étale comparison
statement or change of topology is made in this module.

### Size of `G` relative to the geometric universe

The proposition has one further premise, `OpenQuotientsSmall`: for
every open subgroup `N` of `G`, the coset set `G ⧸ N` is `Small.{v}`,
where `v` is the universe of the analytic spaces and chart indices in
`GSpace.{u,v,v}`. Berkovich's proof uses the induced spaces `U_{G/N}`
of Construction 1.1.2, p. 2: one copy of `U` for each coset of an open
subgroup `N`. Their family `{V_{G/N}(G)}` is cofinal in the category of
étale neighbourhoods of a geometric point of `X(G)` (§1.3, p. 6), and
steps B.2–B.3, pp. 9–10, compute stalks of both sides through it. In
the Library, such disjoint unions are `localizedSigma` and
`InducedSpace.inducedAction`, which index copies by a type in a universe
`z` and land in `LocalizedCategory.{u, max z v, max z v}`. Under the size
premise the index `G ⧸ N` can be replaced by `Shrink (G ⧸ N) : Type v`,
so the copies lie in the same universe `v` as `X`. The premise is a
condition on the coset sets, not on `G`: for instance, open subgroups of
a profinite group have finite index, so it holds for every profinite
`G`. A discrete `G` satisfies it exactly when `G` itself is `v`-small.

Without this premise the proposition is false. With `X` the analytic
point of an algebraically closed complete field, a discrete simple `G`
too large to act nontrivially on any `v`-small space, and the smooth
sheaf of functions with values in the regular module `R[G]`, the
invariant-sheaf functor kills a nonzero smooth sheaf. Then the specified
counit cannot be an isomorphism. The premise excludes this example.
The premise is a size hypothesis only; it does not supply the induced
spaces' Hausdorffness, étaleness or continuity of their actions. Those
are part of Berkovich's construction and remain proof obligations.

## Lean declarations

All declarations are in `Langlands.Sheaf.Equivariant.Analytic`.
The ambient adjunction is the published `etaleSheafInverseImageAdjunction`
from [AnalyticInverseImage](../AnalyticInverseImage.md). Here `b^*` is its
left adjoint `etaleSheafInverseImage`: the sheafification on the twisted
étale site of the inverse image presheaf constructed by a Kan extension.
The right adjoint is `etaleInvariantSheaf`, with sections `F(V)^G`.
The paired documentation of that module explains the use of the twisted
site rather than constructing the two sides of the action separately.

- `EtaleInverseImageSmooth X R hX` abbreviates the property that `b^*E`
  satisfies `smoothSheafProperty` for every module sheaf `E` on
  `equivariantEtaleTopology X`. This means local discreteness for the
  distinguished lifts: the sieve on each object where a section becomes
  discrete after restriction to such lifts must cover that object.
- With a proof of this property, `etaleSmoothInverseImage` factors
  `b^*` through the full subcategory of locally discrete sheaves.
  `etaleSmoothInverseImageAdjunction` restricts the ambient adjunction
  along that full inclusion. Its right adjoint is the existing
  `etaleGSheafInvariantSheaf`, the restriction of `(b_*-)^G` to
  `EtaleGSheaf`. The commuting functor isomorphisms in the restriction
  are identities, so its unit and counit are the ambient maps on the
  indicated objects, with the counit regarded as a smooth-sheaf map.
- `OpenQuotientsSmall.{v, z}` (with `G` implicit) is the Prop
  `∀ N : OpenSubgroup G, Small.{v} (G ⧸ (N : Subgroup G))` described above.
- `EtaleGSheafToposComparisonStatement X R hX` assumes
  `OpenQuotientsSmall` and asserts the existence of the smoothness proof
  and invertibility of **both** natural transformations of this specific
  restricted adjunction. Thus it includes the map `E → (b_*b^*E)^G` and
  the map `b^*((b_*F)^G) → F` as the isomorphisms to be proved. It does
  not choose an arbitrary functor or assume either isomorphism as a
  premise.
- `etaleGSheafEquivalenceOfStatement` packages the equivalence from a
  proof of the proposition and of the size premise, using
  `Adjunction.toEquivalence`. Its functor is the factored inverse image;
  its inverse is the invariant sheaf functor. This categorical
  construction does not prove the geometric proposition.
