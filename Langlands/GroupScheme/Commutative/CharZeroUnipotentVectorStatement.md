# Commutative unipotent groups in characteristic zero are vector groups

`Langlands.GroupScheme.CharZeroCommutativeUnipotentVectorGroupStatement.{u}`
is a proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field with `[CharZero k]` and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]`, `[IsAffineHom G.X.hom]` and
`[IsCommMonObj G.X]`. If `IsUnipotent G`, then `RelativeRoot.IsVectorGroup G`.

The ingredients are existing declarations, used without change.

- `CharZero k` (Mathlib) says that `k` has characteristic zero.
  `IsCommMonObj G.X` (Mathlib) says that the multiplication of the group
  object `G.X` is commutative.
- `IsUnipotent G` (from [`Reductive.Basic`](../Reductive/Basic.md)) says that
  every nonzero finite-dimensional matrix representation of `G` has a
  nonzero fixed vector (Milne 6.45).
- `RelativeRoot.IsVectorGroup G` (from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md))
  says that for some `n : ℕ` there are group isomorphisms, for every scheme
  `T` over the base, between the points of `G` over `T` and the additive
  group of `n`-tuples of global functions on `T`, compatible with pullback
  along every morphism of test schemes. By the Yoneda lemma this says that
  `G` is isomorphic, as a group scheme, to `G_a^n`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 16.15, p.329: "A connected commutative group variety G over a
  perfect field k is a product of a torus and a connected commutative
  unipotent group variety. When k has characteristic zero, every commutative
  unipotent algebraic group is a vector group." This statement formalizes
  the second sentence. Its proof: "a connected commutative unipotent
  algebraic group in characteristic zero is a vector group (14.33)."
- Section 14d, p.288: "In this section, k is a field of characteristic
  zero." After Corollary 14.33, p.289: "In particular, every commutative
  unipotent group over k is isomorphic to G_a^r for some r".
- 2.12, p.43: "An algebraic group U over k is a vector group if it is
  isomorphic to a product of copies of G_a."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."
- Chapter 14 opening, p.279, and Chapter 16 opening, p.324: "Recall that all
  algebraic groups are affine over a base field k."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 16.15 and
its proof on printed p.329 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.43, 135, 279,
288, 289 or 329. Their p.324 entry replaces "diagonalizable" with
"trigonalizable" in the last sentence of the first paragraph of Chapter 16;
it does not concern the affineness sentence. The 2022 errata have no entry
for pp.43, 135, 279, 288, 289, 324 or 329.

## Derivation from the source

- **The group.** A commutative unipotent algebraic group over `k` is a group
  scheme of finite type over `k`, affine by the convention of Chapters 14
  and 16, with commutative multiplication and every nonzero representation
  having a nonzero fixed vector. The statement assumes
  `LocallyOfFiniteType G.X.hom`, `IsAffineHom G.X.hom` (an affine morphism is
  quasi-compact, so `G` is of finite type), `IsCommMonObj G.X` and
  `IsUnipotent G`. No smoothness or connectedness hypothesis is imposed,
  matching "every commutative unipotent algebraic group".
- **Vector group.** By 2.12 a vector group is an algebraic group isomorphic
  to a product of copies of `G_a`, which is `RelativeRoot.IsVectorGroup G`.
  The trivial group is the case `n = 0`.
- **The first sentence of 16.15.** Not part of this statement. For a
  smooth connected commutative affine group over a perfect field, it is a
  consequence of the published theorem `nilpotentPerfectFieldProduct`
  (statement `NilpotentPerfectFieldProductStatement`, Milne 16.48), since a
  commutative group is nilpotent.
- **Related Library statement.** `RelativeRoot.CommutativeUnipotentVectorCharZeroStatement`
  (in `Rational.CommutativeVectorClassificationStatement`) is the case of an
  algebraically closed field and a smooth connected group.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
