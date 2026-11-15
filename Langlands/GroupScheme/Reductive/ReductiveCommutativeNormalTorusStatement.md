# Reductive groups and commutative normal subgroups

`Langlands.GroupScheme.ReductiveCommutativeNormalTorusStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves nothing.

## Statement

The proposition says: for every field `k : Type u` and every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` with `Smooth G.X.hom`,
`IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`, writing
`CommutativeNormalAreTori` for the local proposition

```text
∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
  IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
    IsCommMonObj H.X → (SubgroupFunctor.range j).IsNormal →
      IsTorus H,
```

the proposition is

```text
(IsConnectedReductive G → CommutativeNormalAreTori) ∧
  (PerfectField k → CommutativeNormalAreTori → IsConnectedReductive G).
```

In words: let `G` be a smooth connected affine group scheme over a field `k`.
If `G` is reductive, then every smooth connected commutative normal closed
subgroup of `G` is a torus. Conversely, if `k` is perfect and every smooth
connected commutative normal closed subgroup of `G` is a torus, then `G` is
reductive.

Every ingredient is an existing declaration, used without change:

- `IsConnectedReductive G` (from `Langlands.GroupScheme.Reductive.Basic`) says
  that `G` is smooth, affine and connected and that every smooth connected
  unipotent normal closed subgroup of `G_{k̄}` is trivial
  (`HasTrivialUnipotentRadical`), where `k̄ = AlgebraicClosure k`. This is
  Milne's definition of a reductive group (6.46), as recalled below.
- `IsTorus H` (from `Langlands.GroupScheme.Torus.Lattice`) is the Library's
  predicate for tori over a field: for some field extension `K` of `k` (in
  universe `u`), the base change of `H` to `Spec K` is a split torus
  (`IsSplitTorus`, isomorphic to `splitTorus` on a finite index type, possibly
  empty). This is Milne's Definition 12.14, quoted below. The trivial group is
  a torus of rank zero.
- `IsClosedSubgroup j` says that the morphism of schemes underlying `j` is a
  closed immersion. `SubgroupFunctor.range j` is the image subgroup functor of
  `j` on all test schemes over `Spec k`, and `IsNormal` is normality on every
  test scheme.
- `IsCommMonObj H.X` is Mathlib's class saying that the group law of the group
  object `H.X` is commutative. Since `j` is a monomorphism, `H` is commutative
  exactly when its image in `G` is a commutative subgroup functor.
- `PerfectField k` is Mathlib's class of perfect fields.

The perfectness hypothesis is used only in the converse direction, as in the
source.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

- Proposition 19.12, printed p. 400 (PDF p. 416):

  > PROPOSITION 19.12. Let G be a connected group variety over a field k. If G
  > is reductive, then every smooth connected normal commutative algebraic
  > subgroup is a torus; the converse is true if k is perfect.

  Milne's proof reads in full: "The proof is the same as that of Proposition
  19.3."
- Reductivity, §19.b, printed p. 400 (PDF p. 416): "Recall (6.46) that an
  algebraic group G over a field k is said to be reductive if it is smooth and
  connected and the unipotent radical of G_{k^a} is trivial."
- Tori, Definition 12.14, printed p. 236 (PDF p. 252): "An algebraic group
  over k is a torus if it becomes isomorphic to a finite product of copies of
  Gm over some field containing k."
- Conventions: 1.26, printed p. 13 (PDF p. 29): "group variety" means "smooth
  algebraic group". Printed p. 162 (PDF p. 178), before Chapter 9: "By
  'algebraic group' we shall mean 'affine algebraic group' and by 'group
  variety' we shall mean 'affine group variety'." The `IsAffineHom G.X.hom`
  hypothesis records this convention, which applies to Chapter 19.

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists
Chapter 19 corrections only on p. 399 (Definitions 19.7 and 19.8), Chapter 12
corrections only on pp. 244 and 249 (12.41 and 12.57), Chapter 14 corrections
only on p. 273, and Chapter 16 corrections only on pp. 324, 330 and 349. None
concerns 19.12, 12.14 or the results cited below.

The provenance is derived for three reasons:

1. Milne's "smooth connected normal commutative algebraic subgroup" is a
   closed subgroup `j : H ⟶ G` with `H` smooth, connected and commutative and
   with normal image; "is a torus" is `IsTorus H` for the group scheme `H`.
2. Definition 12.14 allows any field containing `k`; `IsTorus` takes the field
   `K` in the universe `u` of `k`. Since an algebraic closure of `k` lies in
   universe `u`, and a torus split over some extension is split over an
   algebraic closure, this restriction loses nothing. That comparison is not
   formalized.
3. `k` lies in an arbitrary universe `u`. This is a formalization convention.

## For the later proof (not part of this unit)

Milne gives no separate proof. The following adaptation of the proof of
Proposition 19.3 (printed p. 398) is not Milne's text.

Suppose that `G` is reductive and that `H` is a smooth connected commutative
normal subgroup. Over `k^a`, Theorem 16.13(b) (printed p. 328) writes
`H_{k^a} ≃ U × M` with `U` the largest unipotent algebraic subgroup and `M` of
multiplicative type, and `U` is smooth and connected because `H` is (printed
p. 329: "Because G_s and G_u become quotients of G over k^a, they are smooth or
connected if G is smooth or connected."). Conjugation by a point of
`G(k^a)` is an automorphism of `H_{k^a}` over `k^a`, and a unipotent subgroup
maps into `U` under it; so `U(k^a)` is normalized by `G(k^a)`, and `U` is
normal in `G_{k^a}` because `G_{k^a}` is smooth and `k^a` is algebraically
closed. (Note 16.19, printed p. 329, warns that `G_u` is only weakly
characteristic in general, which is why the argument uses points over `k^a`.)
Hence `U ⊆ R_u(G_{k^a}) = e`, so `H_{k^a} = M` is smooth, connected and of
multiplicative type, hence a torus (proof of Corollary 16.15, printed p. 329:
"A smooth connected algebraic group of multiplicative type is a torus"), and
`H` is a torus by Definition 12.14.

For the converse, suppose that `k` is perfect and `G` is not reductive. By
Proposition 19.11(a), printed p. 400 ("If R_u(G) = e, then G is reductive"),
the unipotent radical `R_u(G)` over `k` (the largest smooth connected normal
unipotent subgroup, Corollary 14.8, printed p. 282) is nontrivial. It is
unipotent, hence solvable (Proposition 14.21, printed p. 284), so its derived
series terminates with `e` (Proposition 6.30, printed p. 132). The last
nontrivial term `N` of the derived series is smooth and connected, and it is
characteristic in `R_u(G)` because each term is characteristic in the previous
one (Corollary 6.19(b),(e), printed p. 129: "(b) If G is connected (resp.
smooth), then DG is connected (resp. smooth)" and "(e) DG is a characteristic
subgroup of G"); so `N` is normal in `G`. It is commutative because `DN = e`,
and unipotent by Corollary 14.7 (printed p. 282: "Subgroups, quotients, and
extensions of unipotent algebraic groups are unipotent"). A torus is of
multiplicative type, and Proposition 14.16 (printed p. 284) says: "An
algebraic group that is both multiplicative and unipotent is trivial." So `N`
is a nontrivial smooth connected commutative normal subgroup that is not a
torus.

In the Library, Proposition 19.11 is proved as `perfectFieldPseudoReductive`
(`Langlands.GroupScheme.Reductive.PerfectFieldProof`), and the
scheme-theoretic derived subgroup is `derivedSubgroup`
(`Langlands.GroupScheme.Derived.Basic`).
