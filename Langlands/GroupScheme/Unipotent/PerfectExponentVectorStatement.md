# Groups of exponent `p` over perfect fields are vector groups

`Langlands.GroupScheme.PerfectFieldExponentVectorGroupStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a perfect field (`[PerfectField k]`) of characteristic
`p`, with `[Fact p.Prime]` and `[CharP k p]`. Let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy `[Smooth G.X.hom]`,
`[IsAffineHom G.X.hom]` and `[IsCommMonObj G.X]`. Assume:

- `ConnectedSpace G.X.left`;
- for every scheme `T` over `Spec k` and every point `g : T ⟶ G.X`,
  `g ^ p = 1` in the group of `T`-points of `G`.

The conclusion is

```text
∃ r : ℕ, Nonempty (G ≅ VectorGroup.groupScheme (CommRingCat.of k) r)
```

so `G` is isomorphic, as a group scheme over `Spec k`, to the vector group
`𝔾ₐʳ` for some `r`.

The ingredients are existing declarations, used without change.

- `PerfectField k`, `Fact p.Prime` and `CharP k p` (Mathlib) say that `k` is
  perfect of prime characteristic `p`.
- `Smooth G.X.hom` and `IsAffineHom G.X.hom` (Mathlib) say that the
  structure morphism `G.X.left ⟶ Spec k` is smooth and affine.
- `IsCommMonObj G.X` (Mathlib) says that the multiplication of `G` is
  unchanged when precomposed with the swap of the two factors of `G ×_k G`.
- `g ^ p` is the `p`-th power in the group `T ⟶ G.X` of `T`-points, the group
  structure induced by the group object `G` (Mathlib's
  `CategoryTheory.MonObj` scoped instances).
- `VectorGroup.groupScheme (CommRingCat.of k) r` (from
  [`VectorGroupQuotient`](../VectorGroupQuotient.md)) is the vector group
  `𝔾ₐʳ = Spec k[T₁, …, T_r]` over `Spec k`, with the additive group law.
- `≅` is an isomorphism in `GroupScheme (Spec (CommRingCat.of k))`, that is,
  an isomorphism of group schemes over `Spec k`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 14.54, p.297: "When k is perfect, every smooth connected
  commutative group G of exponent p over a perfect field k is isomorphic to
  G_a^r."
- Section 14e opening, p.292: "In this section, k is a field of
  characteristic p ≠ 0."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k."
- Definition 1.24, p.12: "An algebraic group (G, m) is commutative if
  m ∘ t = m, where t is the transposition map (x, y) ↦ (y, x) : G × G →
  G × G."
- p.8: "The functor R ⇝ (R, +) is represented by Spm(k[T]), and hence is an
  algebraic group Ga."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Proposition 14.54 on
printed p.297 as "When k is perfect, every smooth connected commutative group
G of exponent p over k is isomorphic to G_a^r for some r ≥ 1." Its Section
14e opening, p.292, has the same sentence as the 2017 edition.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.8 or 12.

Milne's proof: such a `G` is elementary unipotent, that is, it embeds into a
vector group (Definition 14.45). The printed proof cites 14.48 for this; the
smooth case is stated as Proposition 14.49. By Theorem 14.46, `G` corresponds
to the module `P(G) ≅ Hom(G, Ga)` over the twisted polynomial ring `k_σ[F]`,
and this module is torsion-free because `G` is connected and smooth. As `k`
is perfect, the module is free (14.51), say of rank `r`, and so
`G ≅ G_a^r`. This is explanation only. The statement does not depend on that
route.

## Derivation from the source

- **Field.** In Section 14e the field has characteristic `p ≠ 0`. The
  statement assumes `[Fact p.Prime]` and `[CharP k p]`, and `[PerfectField k]`
  for "k is perfect".
- **Smooth connected commutative group.** "Group" means algebraic group: a
  group scheme of finite type over `k`, affine by the Chapter 14 convention.
  The statement assumes `Smooth G.X.hom`, `IsAffineHom G.X.hom`,
  `ConnectedSpace G.X.left` and `IsCommMonObj G.X` (Definition 1.24).
  Smoothness gives local finite presentation and affineness gives
  quasi-compactness, so `G` is of finite type over `k`.
- **Exponent `p`.** The hypothesis says that `g ^ p = 1` for all points `g`
  of `G` with values in any scheme over `k`. Taking `T = G.X` and `g` the
  identity morphism of `G.X`, this is the same as saying that the `p`-th power
  morphism `G → G` is the trivial homomorphism: `G` is killed by `p`. For a
  nontrivial `G` this is "exponent `p`". The hypothesis also admits the
  trivial group, for which the conclusion holds with `r = 0`. For nontrivial
  `G` any `r` in the conclusion is at least `1`, since `𝔾ₐ⁰` is trivial. So
  the 2022 bound `r ≥ 1` is implied and is not stated separately.
- **`G_a^r`.** Milne's `Ga` is `Spm(k[T])` with the group law `(R, +)`, and
  `G_a^r` is its `r`-fold product. This is
  `VectorGroup.groupScheme (CommRingCat.of k) r`. "Isomorphic" means
  isomorphic as algebraic groups, which is an isomorphism in
  `GroupScheme (Spec (CommRingCat.of k))`.
- **Universes.** One universe `u` is used for `k` and the schemes. This is a
  formalization convention.

## Related Library results

- `Langlands.GroupScheme.RelativeRoot.smoothCommutativePTorsionVector` (in
  [`Rational.CommutativePTorsionVectorProof`](../Rational/CommutativePTorsionVectorProof.md))
  proves `RelativeRoot.SmoothCommutativePTorsionVectorStatement`, which is
  the case of an algebraically closed field, with the conclusion
  `IsVectorGroup`. By
  `RelativeRoot.isVectorGroupOfDimension_iff_nonempty_iso` (in
  [`Rational.VectorGroupCoordinates`](../Rational/VectorGroupCoordinates.md)),
  `IsVectorGroupOfDimension` is equivalent to an isomorphism with
  `VectorGroup.groupScheme (CommRingCat.of k) n`.
