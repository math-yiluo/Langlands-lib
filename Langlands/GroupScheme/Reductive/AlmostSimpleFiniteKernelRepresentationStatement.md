# Almost-simple groups have simple representations with finite kernel

`Langlands.GroupScheme.AlmostSimpleFiniteKernelRepresentationStatement.{u}`
is a proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field, put `S = Spec (CommRingCat.of k)`, and let
`G : GroupScheme S` satisfy `IsAlmostSimple G`. Then there are `n : ℕ` and
`ρ : MatrixRepresentation G (Fin n)` such that

1. `(⊤ : Submodule k (Fin n → k)) ≠ ⊥`, that is, `n ≠ 0`;
2. every `W : Submodule k (Fin n → k)` with `ρ.IsStableSubspace W` is `⊥`
   or `⊤`;
3. `IsFinite (kernel ρ).X.hom`.

The ingredients are existing declarations, used without change.

- `IsAlmostSimple G` (from [`Reductive.AlmostSimple`](AlmostSimple.md)) says
  that `G` is semisimple (`IsSemisimple G`, which includes
  `IsConnectedReductive G`: smooth, affine, connected, with trivial
  geometric unipotent radical), that `G` is not commutative (two points of
  `G` over some test scheme do not commute), and that every smooth
  connected closed normal subgroup of `G` has range `⊥` or `⊤`.
- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `ρ : G ⟶ GL_n` over `k`, a representation of `G` on `kⁿ`.
- `ρ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says that `W` is a subrepresentation: `ρ(x)(W ⊗ A) ⊆ W ⊗ A` for every
  commutative `k`-algebra `A` and every point `x` of `G` with values in `A`.
- `kernel ρ` (from [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md))
  is the scheme-theoretic kernel of `ρ`, the fibre product of `ρ` with the
  unit section of `GL_n`. `IsFinite` (Mathlib) says that its structure
  morphism to `Spec k` is finite.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Lemma 21.59, p.442 (Section 21f): "Every almost-simple algebraic group has
  a simple representation with finite kernel" (the printed statement has no
  final full stop).
- Its proof: "Every simple subrepresentation of a faithful representation
  on which the group acts nontrivially has finite kernel."
- Chapter 21 opening, p.424: "The field k is arbitrary."
- Definition 4.15, p.90: "A representation of an algebraic group is simple
  if it is ≠ 0 and its only subrepresentations are 0 and itself."
- Definition 19.7, p.399, as printed in 2017: "An algebraic group over k is
  simple (resp. almost-simple) if it is semisimple and noncommutative, and
  every proper normal algebraic subgroup is trivial (resp. finite)."

The official errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`
replaces Definition 19.7 (entry for p.399): "An algebraic group G over k is
almost-simple if it is semisimple and non-commutative and its only smooth
connected normal subgroups are G and e. It is simple if in addition its
centre is trivial." The Library's `IsAlmostSimple` follows this corrected
definition, as explained in [`Reductive.AlmostSimple`](AlmostSimple.md).

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) prints the corrected
Definition 19.7 on p.399, and Lemma 21.59 with the same proof on p.442, in
Section 21f, with the same words. Its Definition 4.15 is on p.90 with the
same words. The errata snapshot `milne-2022-algebraic-groups-errata-2026-11-04`
has no entry for p.90, 399, 424 or 442, and the 2017 errata have no entry
for p.90, 424 or 442.

Milne's proof is a sketch. It uses that the group acts nontrivially on some
simple subrepresentation of a faithful representation, and that a proper
normal algebraic subgroup of an almost-simple group is finite. The latter is
the defining property in the 2017 Definition 19.7; under the corrected
definition a proof has to derive it.

## Derivation from the source

- **The group.** "Almost-simple algebraic group" over the arbitrary field
  `k` is `IsAlmostSimple G`, the corrected Definition 19.7. Smoothness,
  affineness and connectedness are part of `IsSemisimple G`.
- **The representation.** A finite-dimensional representation of `G` on a
  vector space `V` becomes `ρ : MatrixRepresentation G (Fin n)` after
  choosing a basis of `V`, with `n = dim V`; subrepresentations of `V` are
  the subspaces `W` with `ρ.IsStableSubspace W`. "Simple" (Definition 4.15)
  is conjuncts 1 and 2: `kⁿ ≠ 0`, and every subrepresentation is `0` or
  `kⁿ`.
- **Finite kernel.** The kernel of a representation `r : G → GL_V` is the
  kernel of the homomorphism `r`, the fibre product with the identity of
  `GL_V`. This is `kernel ρ`, and "finite" is `IsFinite (kernel ρ).X.hom`.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
