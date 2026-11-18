# Smooth connected groups of dimension one are forms of `𝔾ₘ` or `𝔾ₐ`

`Langlands.GroupScheme.OneDimensionalGroupFormsStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[SmoothOfRelativeDimension 1 G.X.hom]` and `[IsAffineHom G.X.hom]`, and
assume `ConnectedSpace G.X.left`. For a field `K` with `[Algebra k K]`, write
`G_K` for the base change
`(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G`.
The statement is the conjunction of:

1. either there is a field `K : Type u` with `Algebra k K`,
   `FiniteDimensional k K` and `Algebra.IsSeparable k K` such that
   `G_K ≅ (Gm (Spec (CommRingCat.of K))).toGrp`, or there is a field
   `K : Type u` with `Algebra k K`, `FiniteDimensional k K` and
   `IsPurelyInseparable k K` such that
   `G_K ≅ VectorGroup.groupScheme (CommRingCat.of K) 1`;
2. if `k` is algebraically closed (`IsAlgClosed k`), then
   `G ≅ (Gm (Spec (CommRingCat.of k))).toGrp` or
   `G ≅ VectorGroup.groupScheme (CommRingCat.of k) 1`.

Each `≅` is an isomorphism of group schemes over the base, stated as
`Nonempty (_ ≅ _)`.

The ingredients are existing declarations, used without change.

- `SmoothOfRelativeDimension 1 G.X.hom`, `IsAffineHom G.X.hom` and
  `ConnectedSpace G.X.left` (Mathlib) say that the structure morphism
  `G.X.left ⟶ Spec k` is smooth of relative dimension one and affine, and
  that the underlying space of `G` is connected.
- `FiniteDimensional k K`, `Algebra.IsSeparable k K`,
  `IsPurelyInseparable k K` and `IsAlgClosed k` (Mathlib) have their usual
  meanings.
- `GroupScheme.baseChange` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is base
  change of group schemes along `Spec K ⟶ Spec k`.
- `Gm S` (from [`Multiplicative`](../Multiplicative.md)) is the multiplicative
  group over a scheme `S`, whose points with values in a scheme `T` over `S`
  are the units of `Γ(T, 𝒪_T)`; `.toGrp` is its underlying group scheme.
- `VectorGroup.groupScheme (CommRingCat.of K) 1` (from
  [`VectorGroupQuotient`](../VectorGroupQuotient.md)) is the additive group
  `𝔾ₐ = Spec K[T]` over `Spec K`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 16.16, p.329: "Let G be a smooth connected algebraic group of
  dimension 1 over a field k. Either G becomes isomorphic to Gm over a finite
  separable extension of k or it becomes isomorphic to Ga over a finite
  purely inseparable extension of k. Over an algebraically closed field, Ga
  and Gm are the only connected group varieties of dimension 1."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."
- p.8: "The functor R ⇝ (R, +) is represented by Spm(k[T]), and hence is an
  algebraic group Ga. Similarly, the functor R ⇝ (R^×, ×) is represented by
  Spm(k[T, T⁻¹]), and hence is an algebraic group Gm."
- p.13, after Proposition 1.26: "Therefore 'group variety' = 'smooth
  algebraic group'."
- p.17, "The dimension of an algebraic group": the irreducible components of
  an algebraic group are its connected components, and "The dimension dim(G)
  of G is the common dimension of its connected components".

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 16.16 on
printed p.329 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.8, 13, 17 or
329. Their p.324 entry replaces "diagonalizable" by "trigonalizable" in the
last sentence of the first paragraph of Chapter 16; it does not concern the
affineness sentence quoted above. The 2022 errata have no entry for p.329.
Their p.321 entry restricts Theorem 15.37 to commutative groups and notes
that it is used only in the proof of 16.13, where the groups are
commutative.

Milne's proof: "The group G is commutative (14.25), and so it contains a
multiplicative subgroup G_s such that G/G_s is unipotent. Either G = G_s,
which gives the first case, or G = G_u, which gives the second case
(14.53)." The 2022 reprint adds a reference to 12.19 for the first case.
This is explanation only. The statement does not depend on that route.

## Derivation from the source

- **Smooth connected algebraic group of dimension 1.** An algebraic group in
  Milne is a group scheme of finite type over `k`, affine by the Chapter 16
  convention. The statement assumes `IsAffineHom G.X.hom`, smoothness
  through the relative-dimension instance, and `ConnectedSpace G.X.left`.
  Smoothness gives local finite presentation and affineness gives
  quasi-compactness, so `G` is of finite type over `k`. The instance
  `SmoothOfRelativeDimension 1 G.X.hom` says that `G` is smooth over `k` of
  relative dimension one at every point. For a scheme smooth over a field,
  the relative dimension at a point is the dimension of the scheme at that
  point. `G` is connected, so it is irreducible (p.17), and this is Milne's
  `dim(G) = 1`. Conversely, a smooth connected `G` with `dim(G) = 1` is
  smooth of relative dimension one at every point.
- **Becomes isomorphic over an extension.** "G becomes isomorphic to Gm over
  a finite separable extension of k" means that for some finite separable
  field extension `K` of `k`, the group `G_K` over `K` is isomorphic to `Gm`
  over `K`. The extension is a field `K : Type u` with an algebra structure
  over `k`, finite-dimensional and separable. The second alternative uses a
  finite purely inseparable extension in the same way. Milne's `Gm` and `Ga`
  over `K` are the functors `R ⇝ R^×` and `R ⇝ R` on `K`-algebras (p.8),
  which are `Gm (Spec K)` and `VectorGroup.groupScheme (CommRingCat.of K) 1`.
  "Isomorphic" means isomorphic as algebraic groups over `K`, an isomorphism
  in `GroupScheme (Spec (CommRingCat.of K))`. "Either … or" is an inclusive
  disjunction; the two cases cannot both occur, since `Gm` and `Ga` do not
  become isomorphic over any field.
- **Algebraically closed fields.** "Over an algebraically closed field, Ga
  and Gm are the only connected group varieties of dimension 1" is part 2. A
  connected group variety of dimension 1 is a smooth connected algebraic
  group of dimension 1 (p.13), which is the hypothesis of the statement. That
  `Ga` and `Gm` are themselves connected group varieties of dimension 1 is
  not part of the statement.
- **Universes.** One universe `u` is used for `k`, the extension fields `K`
  and the schemes. Every finite extension of `k` is isomorphic to one in
  universe `u`. This is a formalization convention.

## Related Library results

- `Langlands.GroupScheme.OneDimensionalCommutativeStatement` (in
  [`Unipotent.OneDimensionalCommutativeStatement`](../Unipotent/OneDimensionalCommutativeStatement.md))
  states Milne 14.25: such a `G` is commutative.
- `Langlands.GroupScheme.PerfectFieldOneDimensionalUnipotentStatement` (in
  [`Unipotent.OneDimensionalStatement`](../Unipotent/OneDimensionalStatement.md))
  states that over a perfect field a smooth connected affine unipotent group
  of dimension one is a one-dimensional vector group
  (`RelativeRoot.IsVectorGroupOfDimension U 1`).
