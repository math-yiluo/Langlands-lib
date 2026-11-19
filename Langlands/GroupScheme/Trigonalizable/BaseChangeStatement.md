# Trigonalizability is preserved by field extension

`Langlands.GroupScheme.TrigonalizableBaseChangeStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k K : Type u` be fields with `[Algebra k K]`, and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. If
`IsTrigonalizable G`, then `IsTrigonalizable G_K`, where `G_K` is the base
change
`(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G`.

The ingredients are existing declarations, used without change.

- `IsTrigonalizable G` (from [`Trigonalizable`](../Trigonalizable.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero coordinate vector spanning a stable line: every point of `G`, with
  values in any scheme over `Spec k`, maps it to a multiple of itself. This
  is Milne's Definition 16.1, as recorded in that module.
  For `G_K` the field is `K`.
- `GroupScheme.baseChange` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is base
  change of group schemes along `Spec K ⟶ Spec k`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 16.4, p.325: "Let G be an algebraic group over k, and let k′ be
  a field containing k. If G is trigonalizable, then so also is G_k′."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 16.4 on
printed p.325 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for p.325; their p.324
entry concerns the first paragraph of Chapter 16, not the affineness
sentence. The 2022 errata have no entry for pp.324 or 325.

Milne's proof: "An embedding G ↪ T_n gives an embedding G_k′ ↪ T_nk′ by
extension of scalars." Here `T_n` is the group of invertible upper
triangular matrices, and the embedding comes from Proposition 16.2(c). This
is explanation only. The statement does not depend on that route.

## Derivation from the source

- **Algebraic group.** Milne's algebraic group is a group scheme of finite
  type over `k`, affine by the Chapter 16 convention. The statement assumes
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`; an affine morphism
  is quasi-compact, so `G` is of finite type over `k`.
- **Field containing `k`.** A field `k′` containing `k` is a field `K` with
  an algebra structure over `k`, and `G_k′` is the base change of `G` along
  `Spec K ⟶ Spec k`. Any field extension is injective, so no further
  hypothesis on `K` is needed.
- **Universes.** One universe `u` is used for the fields and the schemes.
  This is a formalization convention.
