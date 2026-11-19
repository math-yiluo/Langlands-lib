# Unipotence via nilpotent differentials of representations

`Langlands.GroupScheme.UnipotentNilpotentDifferentialStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy `[Smooth G.X.hom]`,
`[IsAffineHom G.X.hom]` and `[ConnectedSpace G.X.left]`. The statement is
the conjunction of two equivalences.

1. `IsUnipotent G` holds if and only if, for every `n : ℕ`, every
   `ρ : MatrixRepresentation G (Fin n)` and every `X : lieKernel G k`,
   `IsNilpotent (ρ.tangentMatrix k X)`.
2. `IsUnipotent G` holds if and only if there are `n : ℕ` and
   `ρ : MatrixRepresentation G (Fin n)` with `IsClosedSubgroup ρ` such that
   `IsNilpotent (ρ.tangentMatrix k X)` for every `X : lieKernel G k`.

The ingredients are existing declarations, used without change.

- `IsUnipotent G` and `IsClosedSubgroup ρ` (from
  [`Reductive.Basic`](../Reductive/Basic.md)): every nonzero
  finite-dimensional matrix representation of `G` has a nonzero fixed
  vector; and the underlying morphism of schemes of `ρ` is a closed
  immersion.
- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `G ⟶ GeneralLinear.groupScheme (Fin n) k`.
- `lieKernel G k` (from [`Lie.DualNumberKernel`](DualNumberKernel.md)) is the
  kernel of the reduction map `G(k[ε]) → G(k)` on points with values in the
  dual numbers `k[ε]`, `ε² = 0`.
- `ρ.tangentMatrix k X` (from
  [`Lie.RepresentationDifferential`](RepresentationDifferential.md)) is the
  `n × n` matrix `A` with entries in `k` such that the image of `X` under
  `ρ` in `GL_n(k[ε])` is `1 + εA`.
- `IsNilpotent` is from Mathlib: some power of the matrix is zero.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 16.61, p.346: "Let G be a connected group variety. The
  following conditions are equivalent: (a) G is unipotent; (b) The centre of
  G is unipotent and g is nilpotent; (c) For every representation (V, r) of
  G, dr maps the elements of g to nilpotent endomorphisms of V; (d) The
  condition in (c) holds for one faithful representation (V, r) of G."
- Section 4a, p.83: "A linear representation r is faithful if
  r(R): G(R) → Aut_{R-linear}(V_R) is injective for all k-algebras R. For
  finite-dimensional linear representations, this is equivalent to r being
  a closed immersion (3.35)."
- Corollary 4.8, p.86: "Every representation of G is a filtered union of
  its finite-dimensional subrepresentations."
- 10.6, p.188: "Let G be an algebraic group over k. The tangent space of G
  at the neutral element e is L(G) = Ker(G(k[ε]) → G(k)), ε² = 0." On the
  same page Milne identifies `L(G)` with `Lie(G)` and writes `g` for
  `Lie(G)`.
- p.13: "“group variety” = “smooth algebraic group”."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every
  nonzero representation of G has a nonzero fixed vector."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."

Milne's proof of the parts stated here, for orientation only:
(a)⇒(c) because, in a suitable basis of `V`, `G` maps into the group `U_n`
of upper triangular matrices with `1` on the diagonal (14.3); (c)⇒(d)
trivially; (d)⇒(a) by reducing to an algebraically closed field (14.9). If
`G` contains a subgroup `H ≅ G_m`, then `V` decomposes into weight spaces
`V_n` of `H`, and a nonzero `x ∈ Lie(H)` acts on `V_n` as multiplication by
`nx`, contradicting the hypothesis; a connected group variety containing no
such subgroup is unipotent by Proposition 16.60. Milne leaves one point
implicit: in characteristic `p`, the faithfulness of `V` makes the weights
of `H` generate `ℤ`, so some weight `n` with `nx ≠ 0` occurs.

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 16.61 on
printed p.346 with the same words. In the reprint, the definition of a
faithful representation is on p.83, Corollary 4.8 on p.86 and 10.6 on
p.188.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.13, 83, 86,
135, 188, 346 or 347. Their p.324 entry replaces "diagonalizable" with
"trigonalizable" in the last sentence of the first paragraph of Chapter 16;
it does not concern the affineness sentence. The 2022 errata have no entry
for pp.83, 86, 135, 188, 324, 346 or 347; their p.13 entry reverses a dimension
inequality (the group-variety sentence is on p.14 of the reprint, which has
no entry).

## Derivation from the source

- **Scope.** The statement formalizes conditions (a), (c) and (d) of
  Corollary 16.61 and their equivalence. Condition (b) (unipotent centre
  and nilpotent Lie algebra) is not stated. It is not claimed here.
- **The group.** A connected group variety is a smooth algebraic group
  (p.13), affine by the Chapter 16 convention, with connected underlying
  space: `Smooth G.X.hom` (so `G` is locally of finite type),
  `IsAffineHom G.X.hom` (so quasi-compact, hence of finite type) and
  `ConnectedSpace G.X.left`.
- **(a).** Unipotence (6.45) is `IsUnipotent G`.
- **Representations.** Part 1 tests every finite-dimensional
  representation, written as a matrix representation on `kⁿ` after choosing
  a basis. For an infinite-dimensional representation, a nilpotent
  endomorphism with a uniform exponent can fail to exist even for `G_a`
  (the derivation `d/dt` on `O(G_a) = k[t]` in characteristic `0`), so
  condition (c) is read for finite-dimensional representations. Since every
  representation is a filtered union of finite-dimensional ones
  (Corollary 4.8), this is the same as requiring every element of `g` to
  act locally nilpotently on every representation.
- **The Lie algebra and the differential.** `g = Lie(G)` is identified with
  `L(G) = Ker(G(k[ε]) → G(k))` (10.6), which is `lieKernel G k`. The
  differential `dr` sends `X ∈ L(G)` to the element `r(X)` of
  `L(GL_V) = {1 + εA}`, that is to the endomorphism `A` of `V`. In matrix
  form this is `ρ.tangentMatrix k X`.
- **(c) and (d).** "`dr` maps the elements of `g` to nilpotent
  endomorphisms" is `IsNilpotent (ρ.tangentMatrix k X)` for every `X`. A
  faithful finite-dimensional representation is one whose homomorphism to
  `GL_V` is a closed immersion (p.83), which is `IsClosedSubgroup ρ`. So (d)
  is the right-hand side of part 2, and (c) the right-hand side of part 1.
- **Related Library results.** The theorem
  `MatrixRepresentation.isNilpotent_tangentMatrix_of_isUnipotent` (in
  [`Lie.UnipotentTangent`](UnipotentTangent.md)) proves the forward
  direction of part 1 for every group scheme over a field.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
