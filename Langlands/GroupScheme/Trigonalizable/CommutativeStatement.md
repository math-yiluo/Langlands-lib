# Commutative groups over algebraically closed fields are trigonalizable

`Langlands.GroupScheme.AlgClosedCommutativeTrigonalizableStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be an algebraically closed field (`[IsAlgClosed k]`) and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]`, `[IsAffineHom G.X.hom]` and
`[IsCommMonObj G.X]`. Then `IsTrigonalizable G`.

The ingredients are existing declarations, used without change.

- `IsTrigonalizable G` (from [`Trigonalizable`](../Trigonalizable.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero coordinate vector spanning a stable line: every point of `G`, with
  values in any scheme over `Spec k`, maps it to a multiple of itself. This
  is Milne's Definition 16.1, as recorded in that module.
- `IsCommMonObj G.X` (Mathlib) says that the multiplication of `G` is
  unchanged when precomposed with the swap of the two factors of `G ×_k G`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 16.14, p.329: "Every commutative algebraic group over an
  algebraically closed field is trigonalizable."
- Definition 1.24, p.12: "An algebraic group (G, m) is commutative if
  m ∘ t = m, where t is the transposition map (x, y) ↦ (y, x) : G × G →
  G × G."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 16.14 on
printed p.329 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.12 or 329; their
p.324 entry concerns the first paragraph of Chapter 16, not the affineness
sentence. The 2022 errata have no entry for pp.324 or 329. Their p.321 entry
restricts Theorem 15.37 to commutative groups and notes that it is used only
in the proof of Theorem 16.13, where the groups are commutative.

Milne's proof: "The group satisfies condition (b) of Theorem 16.6." That
condition is the existence of a normal unipotent subgroup `G_u` with `G/G_u`
of multiplicative type, supplied for commutative groups by Theorem 16.13.
This is explanation only. The statement does not depend on that route.

## Derivation from the source

- **Algebraic group.** Milne's algebraic group is a group scheme of finite
  type over `k`, affine by the Chapter 16 convention. The statement assumes
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`; an affine morphism
  is quasi-compact, so `G` is of finite type over `k`.
- **Commutative.** Milne's Definition 1.24 is invariance of the
  multiplication under the transposition of the factors, which is
  `IsCommMonObj G.X`.
- **Algebraically closed.** `IsAlgClosed k` is Mathlib's notion.
- **Universes.** One universe `u` is used for the fields and the schemes.
  This is a formalization convention.
