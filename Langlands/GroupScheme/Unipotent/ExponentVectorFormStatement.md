# Groups of exponent `p` are forms of vector groups

`Langlands.GroupScheme.ExponentVectorGroupFormStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field of characteristic `p`, with `[Fact p.Prime]` and
`[CharP k p]`. Let `K : Type u` be a field with `[Algebra k K]`,
`[PerfectField K]` and `[IsPurelyInseparable k K]`. Let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy `[Smooth G.X.hom]`,
`[IsAffineHom G.X.hom]` and `[IsCommMonObj G.X]`. Assume:

- `ConnectedSpace G.X.left`;
- for every scheme `T` over `Spec k` and every point `g : T ⟶ G.X`,
  `g ^ p = 1` in the group of `T`-points of `G`.

The conclusion is

```text
∃ r : ℕ, Nonempty ((GroupScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
    VectorGroup.groupScheme (CommRingCat.of K) r)
```

so the base change of `G` to `K` is isomorphic, as a group scheme over
`Spec K`, to the vector group `𝔾ₐʳ` over `K` for some `r`.

The ingredients are existing declarations, used without change.

- `Fact p.Prime` and `CharP k p` (Mathlib) say that `k` has prime
  characteristic `p`.
- `PerfectField K` and `IsPurelyInseparable k K` (Mathlib) say that `K` is a
  perfect field and an algebraic, purely inseparable extension of `k`.
- `Smooth G.X.hom`, `IsAffineHom G.X.hom` and `IsCommMonObj G.X` (Mathlib)
  say that `G` is smooth and affine over `k` and commutative.
- `g ^ p` is the `p`-th power in the group `T ⟶ G.X` of `T`-points, the group
  structure induced by the group object `G` (Mathlib's
  `CategoryTheory.MonObj` scoped instances).
- `GroupScheme.baseChange` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is base
  change of group schemes along a morphism of base schemes, here
  `Spec K ⟶ Spec k`.
- `VectorGroup.groupScheme (CommRingCat.of K) r` (from
  [`VectorGroupQuotient`](../VectorGroupQuotient.md)) is the vector group
  `𝔾ₐʳ = Spec K[T₁, …, T_r]` over `Spec K`, with the additive group law.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 14.56, p.297: "Every smooth connected commutative algebraic group
  of exponent p is a form of G_a^r for some r." Its proof: "It becomes
  isomorphic to G_a^r over a perfect closure of the base field."
- Section 14e opening, p.292: "In this section, k is a field of
  characteristic p ≠ 0."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k."
- Section 3k, "Forms of algebraic groups", p.76: "Let G be an algebraic group over k, and let K be a
  field containing k. A K/k-form of G is an algebraic group G′ over k that
  becomes isomorphic to G over K."
- "Conventions and notation", p.3: "k^s (resp. k^i) denotes the separable
  (resp. perfect) closure of k in k^a."
- Definition 1.24, p.12: "An algebraic group (G, m) is commutative if
  m ∘ t = m, where t is the transposition map (x, y) ↦ (y, x) : G × G →
  G × G."
- p.8: "The functor R ⇝ (R, +) is represented by Spm(k[T]), and hence is an
  algebraic group Ga."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 14.56 on
printed p.297 as "Every smooth connected commutative algebraic group of
exponent p is a form of G_a^r for some r ≥ 1", with the same proof. Its
Section 14e opening, p.292, has the same sentence as the 2017 edition.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.3, 8, 12 or 76.

Milne's proof applies Proposition 14.54 (over a perfect field, such a group
is isomorphic to `G_a^r`) to the base change of `G` to a perfect closure of
`k`. The base change is still smooth, affine, commutative and killed by
`p`, and it is connected because `Spec K → Spec k` is a universal
homeomorphism for a purely inseparable extension `K` of `k`. This is explanation only. The
statement does not depend on that route.

## Derivation from the source

- **Field.** In Section 14e the field has characteristic `p ≠ 0`. The
  statement assumes `[Fact p.Prime]` and `[CharP k p]`. No perfectness of `k`
  is assumed.
- **Smooth connected commutative algebraic group.** An algebraic group is a
  group scheme of finite type over `k`, affine by the Chapter 14 convention.
  The statement assumes `Smooth G.X.hom`, `IsAffineHom G.X.hom`,
  `ConnectedSpace G.X.left` and `IsCommMonObj G.X` (Definition 1.24).
  Smoothness gives local finite presentation and affineness gives
  quasi-compactness, so `G` is of finite type over `k`.
- **Exponent `p`.** The hypothesis says that `g ^ p = 1` for all points `g`
  of `G` with values in any scheme over `k`. Taking `T = G.X` and `g` the
  identity morphism of `G.X`, this is the same as saying that the `p`-th
  power morphism `G → G` is the trivial homomorphism: `G` is killed by `p`.
  For a nontrivial `G` this is "exponent `p`". The hypothesis also admits the
  trivial group, for which the conclusion holds with `r = 0`. For nontrivial
  `G` any `r` in the conclusion is at least `1`, since `𝔾ₐ⁰` is trivial and
  base change of a nontrivial group to a field extension is nontrivial. So
  the 2022 bound `r ≥ 1` is implied and is not stated separately.
- **Form of `G_a^r`.** By Section 3k, `G` is a `K/k`-form of `G_a^r` when its
  base change to `K` is isomorphic to `G_a^r` over `K`. The statement asserts
  this for `K` a perfect closure of `k`, the field over which Milne's proof
  establishes the isomorphism. A perfect closure is described by
  `PerfectField K` and `IsPurelyInseparable k K`. Every such `K` is
  isomorphic over `k` to `k^i`, the perfect closure of `k` in `k^a`: `K`
  embeds into `k^a` over `k` because it is algebraic, its image is purely
  inseparable over `k` and so lies in `k^i`, and it contains `k^i` because it
  is perfect. So quantifying over all such `K` is the same as asserting the
  isomorphism over `k^i`.
- **`G_a^r`.** Milne's `Ga` is `Spm(k[T])` with the group law `(R, +)`, and
  `G_a^r` over `K` is `VectorGroup.groupScheme (CommRingCat.of K) r`.
  "Isomorphic" means isomorphic as algebraic groups over `K`, which is an
  isomorphism in `GroupScheme (Spec (CommRingCat.of K))`.
- **Universes.** One universe `u` is used for `k`, `K` and the schemes. This
  is a formalization convention.

## Related Library results

- `Langlands.GroupScheme.RelativeRoot.smoothCommutativePTorsionVector` (in
  [`Rational.CommutativePTorsionVectorProof`](../Rational/CommutativePTorsionVectorProof.md))
  proves `RelativeRoot.SmoothCommutativePTorsionVectorStatement`: over an
  algebraically closed field of characteristic `p`, a smooth connected
  commutative affine group killed by `p` satisfies `IsVectorGroup`. This is
  the analogous classification over an algebraically closed field.
