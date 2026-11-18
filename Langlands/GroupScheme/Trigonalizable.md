# Trigonalizable group schemes over a field

This module defines stable lines of matrix representations and trigonalizable
group schemes over a field (Milne, Definition 16.1). It proves that a fixed
vector spans a stable line and that unipotent group schemes are
trigonalizable. The selected declaration is
`Langlands.GroupScheme.IsTrigonalizable`.

## Declarations

Fix `R : CommRingCat`, a group scheme `G` over `Spec R` and a finite index
type `n : Type` with decidable equality. A `MatrixRepresentation G n` (from
[`MatrixRepresentation`](MatrixRepresentation.md)) is a homomorphism of group
schemes `G ⟶ GL_n`, and `ρ.pointMatrix T g` is the invertible matrix over
`Γ(T, 𝒪_T)` attached to a point `g ∈ G(T)`. `scalarMap T : R →+* Γ(T, 𝒪_T)`
(from [`Reductive.Basic`](Reductive/Basic.md)) is the structure ring map of a
scheme `T` over `Spec R`.

- `MatrixRepresentation.IsStableLine ρ v`, for `v : n → R`, holds when for
  every scheme `T` over `Spec R` and every point `g : T ⟶ G.X` there is
  `c : Γ(T, 𝒪_T)` with `ρ(g) · v_T = c • v_T`, where `v_T` is the image of
  `v` in `Γ(T, 𝒪_T)ⁿ` under `scalarMap T`. In words, `ρ(g)` maps `v` to a
  multiple of itself, for points with values in every scheme.
- `MatrixRepresentation.IsFixedVector.isStableLine` proves that a fixed vector
  (`ρ.IsFixedVector v`, from [`Reductive.Basic`](Reductive/Basic.md)) spans a
  stable line, taking every multiplier `c = 1`.
- `IsTrigonalizable G`, for a field `k : Type u` and a group scheme `G` over
  `Spec k`, holds when for every nonempty finite index type `n : Type` with
  decidable equality and every `ρ : MatrixRepresentation G n` there is a
  nonzero `v : n → k` with `ρ.IsStableLine v`.
- `IsUnipotent.isTrigonalizable` proves `IsUnipotent G → IsTrigonalizable G`.
  `IsUnipotent G` (from [`Reductive.Basic`](Reductive/Basic.md)) gives a
  nonzero fixed vector in every nonzero matrix representation, and that
  vector spans a stable line.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Definition 16.1, p.324: "An algebraic group G is trigonalizable if every
  simple representation has dimension one."
- The paragraph after Definition 16.1, p.324: "In other words, G is
  trigonalizable if every nonzero representation of G contains an
  eigenvector. ... Both unipotent and diagonalizable algebraic groups are
  trigonalizable (6.45, 12.12)."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."
- Section 4a, p.83: "A linear representation of G is a homomorphism
  r: G → GL_V of group-valued functors."
- Proposition 4.3, p.85: for a finite-dimensional representation
  `r : G → GL_V` and a subspace `W` of `V`, "The functor
  R ⇝ G_W(R) = {g ∈ G(R) | g(W_R) = W_R} is represented by an algebraic
  subgroup G_W of G."
- Definition 4.15, p.90: "A representation of an algebraic group is simple if
  it is ≠ 0 and its only subrepresentations are 0 and itself."
- Proposition 4.16, p.90: "Every simple representation of an algebraic group
  is finite-dimensional."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Definition 16.1 and
the following paragraph on printed p.324 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.83, 90 or 135.
Their p.324 entry replaces "diagonalizable" by "trigonalizable" in the last
sentence of the first paragraph of Chapter 16 (the 2022 reprint already reads
"trigonalizable" there); it does not concern Definition 16.1. Their p.85
entry says that `G_W` is the stabilizer of `W` in `G` (not `V`), correcting
the name given to the subgroup after Proposition 4.3; it does not change the
functor `G_W`. The 2022 errata have no entry for pp.83, 85, 90, 135 or 324.

## Derivation from the source

- **Representations as matrix representations.** A finite-dimensional
  representation `r : G → GL_V` becomes a matrix representation once a basis
  of `V`, indexed by a finite type `n`, is chosen. A nonzero representation
  has `n` nonempty. Milne works with points with values in `k`-algebras `R`;
  here the test objects are all schemes `T` over `Spec k`. For affine `G`,
  which is Milne's setting, a point of `G` with values in `T` is the same as
  a point with values in the `k`-algebra `Γ(T, 𝒪_T)`, and every `k`-algebra
  `R` is `Γ(Spec R)`. So the two kinds of tests agree.
- **One-dimensional subrepresentations.** A subrepresentation is a subspace
  `W` with `G_W = G`, that is, `g(W_R) = W_R` for every `k`-algebra `R` and
  every `g ∈ G(R)` (Proposition 4.3). For a line `W = k·v`, `v ≠ 0`, this
  says that `r(g)` maps `v` to an element of `R·v` for all `R` and `g`: the
  inclusion `g(W_R) ⊆ W_R` for all points implies equality, because it also
  holds for `g⁻¹`. This is `IsStableLine` for the coordinate vector of `v`.
  Milne's "eigenvector" in the paragraph after Definition 16.1 is such a
  vector.
- **Trigonalizable.** Definition 16.1 asks that every simple representation
  have dimension one. This is equivalent to every nonzero finite-dimensional
  representation having a one-dimensional subrepresentation. If every simple
  representation has dimension one, a nonzero finite-dimensional
  representation contains a nonzero subrepresentation of least dimension,
  which is simple, hence a line. Conversely, a simple representation is
  finite-dimensional (Proposition 4.16), so it contains a line, which by
  simplicity is all of it. The second form is the paragraph after
  Definition 16.1, and it is `IsTrigonalizable`.
- **Scope.** Milne's algebraic groups are affine of finite type over `k`
  (Chapter 16 opening). The Lean predicate is stated for every group scheme
  over `k`, as is `IsUnipotent`; statements using it impose finiteness and
  affineness as their sources require.
- **Unipotent groups.** `IsUnipotent.isTrigonalizable` is the first half of
  Milne's remark "Both unipotent and diagonalizable algebraic groups are
  trigonalizable". The diagonalizable half is not proved here.
- **Universes.** The field lives in an arbitrary universe `u`, and the index
  types `n` live in `Type`, as in `MatrixRepresentation` and `IsUnipotent`.

## Related Library results

- `Langlands.GroupScheme.IsUnipotent` and
  `Langlands.GroupScheme.MatrixRepresentation.IsFixedVector` (in
  [`Reductive.Basic`](Reductive/Basic.md)) are the fixed-vector analogues of
  `IsTrigonalizable` and `IsStableLine`.
