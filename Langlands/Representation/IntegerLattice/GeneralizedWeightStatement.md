# Simultaneous generalized weights of commuting invertible tuples

Author: Worker 277.

`Langlands.CommutingTupleGeneralizedWeightDecompositionStatement.{u}` is a
closed Prop-valued definition in
`Langlands.Representation.IntegerLattice.GeneralizedWeightStatement`. It
states the basis-free decomposition into simultaneous generalized weight
spaces that underlies the block choice in David Renard, *Représentations
des groupes réductifs p-adiques*, French version dated 9 July 2026,
Appendix C.III, printed pp.279–280, one-based PDF285–286. Both pages were
read directly. The original source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

The file proves nothing. It records only the proposition.

## Hypotheses

The proposition quantifies over every natural `d` and every carrier
`V : Type u` in an arbitrary universe `u`. The carrier has an
`AddCommGroup` and a complex `Module` structure and satisfies
`FiniteDimensional ℂ V`. This matches the source's
"espace vectoriel sur C de dimension finie".

The last datum is a tuple
`A : Langlands.IntegerLattice.CommutingInvertibleTuple d V`, the published
construction in `Langlands.Representation.IntegerLattice`. Its entries
`A.1 i` are actual units of `Module.End ℂ V`, so each entry includes its
two-sided inverse. Its proof component `A.2` asserts that distinct entries
commute. These are the source's `u_1, …, u_d`, "des endomorphismes
inversibles de V commutant deux à deux". The coordinate type `Fin d`
shifts the source's one-based indices by one.

No further hypothesis appears. In particular there is no
diagonalizability, nontriviality, distinctness, basis or block choice,
and no supplied decomposition or supplied finite family of labels. The
cases `d = 0` and `V = 0` are included.

## Block construction

For `c : Fin d → ℂˣ`, the block is

```
W(c) = ⨅ i : Fin d, (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ)
```

This intersection of submodules of `V` is written out in each clause; the
file introduces no new definition. Mathlib's
`Module.End.maxGenEigenspace f μ` is the maximal generalized eigenspace,
the submodule of vectors `x` with `((f - μ • 1) ^ k) x = 0` for some
natural `k`. Thus `W(c)` consists of the vectors killed by some power of
every `u_i - c_i`. On a subspace invariant under all `u_i`, the condition
that every `u_i - c_i` is nilpotent there is equivalent to every diagonal
entry of `u_i` in a triangular basis of that subspace being `c_i`; this is
how the source describes its blocks.

The labels range over all tuples of nonzero complex numbers. The source
gives each character `χ_j` by "un d-uplet (z^{(j)}_1 … z^{(j)}_d) de
nombres complexes non nuls". A character of `ℤ^d` is determined by its
values on the standard generators, so unit tuples are the source's
character labels.
For the unique tuple at `d = 0`, `W(c)` is the empty intersection, the
whole space. When `V = 0` every block is the zero submodule.

## The four assertions

For every `d`, `V` and `A` as above, the proposition is the conjunction of
the following.

1. **Finite support.** The set
   `{c : Fin d → ℂˣ | W(c) ≠ ⊥}` is `Set.Finite`. This is the complete
   nonzero support of the actual intersections, not a supplied family.
2. **Independence.** `iSupIndep W`: every block meets the supremum of all
   other blocks only in zero.
3. **Spanning.** `⨆ c, W(c) = ⊤`.
4. **Invariance under the lattice action.** For every `c` and every
   `n : Langlands.IntegerLattice.Lattice d`, the underlying map of
   `Langlands.IntegerLattice.tupleRepresentationEquiv d V A n` satisfies
   `Set.BijOn` from `W(c)` to `W(c)`. That is, it maps `W(c)` into itself,
   is injective on `W(c)`, and every vector of `W(c)` is the image of a
   vector of `W(c)`.

Assertions 1–3 together say that the nonzero blocks, finitely many,
form an internal direct sum decomposition of `V`. The proposition
expresses this through the unit-indexed family itself, with the
zero blocks included, not through a selected finite index type.

In assertion 4, `IntegerLattice.Lattice d` abbreviates
`Multiplicative (Fin d → ℤ)`, the whole integer lattice, so negative and
mixed-sign coordinates are included. The map is the representation
constructed from `A` by the published equivalence. The published theorem
`Langlands.IntegerLattice.tupleRepresentationEquiv_apply` identifies it
with the finite product of the integer powers `A.1 i ^ n.toAdd i`, which
is the source's `U(n) = u_1^{n_1} ∘ ⋯ ∘ u_d^{n_d}`. Bijectivity on each
block is the basis-free form of the invertibility of the source's blocks
`A_j(n)`.

## Relation to the source and provenance

The source proof (PDF285–286) first notes that the commuting `u_i` have
common eigenspaces and lists the distinct characters
`χ_1, …, χ_l` from their simultaneous eigenvalues. It then chooses "une
base de triangularisation commune des u_1, …, u_d de telle sorte que pour
tout n ∈ ℤ^d, la matrice A(n) de U(n) dans cette base soit diagonale par
bloc, de blocs A_j(n), A_j(n) étant une matrice triangulaire supérieure
dont les éléments diagonaux sont de la forme χ_j(n)".

The source does not separately state a decomposition. The proposition
here is derived from that choice. The basis vectors of block `j` span a
subspace `V_j`. The block-diagonal form for every `n` makes every `V_j`
invariant under every `U(n)`, and `V` is the direct sum of the `V_j`.
On `V_j` each `u_k` is triangular with constant diagonal `z^{(j)}_k`, so
`u_k - z^{(j)}_k` is nilpotent there, and the labels of distinct blocks
differ. Hence `V_j` is contained in the simultaneous generalized weight
space `W(z^{(j)})`. Since the `V_j` span `V` and the blocks `W(c)` are
independent, `V_j = W(z^{(j)})`, and every other `W(c)` is zero. The
proposition states this decomposition without a basis, for the actual
blocks `W(c)`. It records the decomposition the source's choice
presupposes. It does not assert that a common triangular basis exists.

The proposition does not identify the support with the source's list of
characters, that is, it does not assert that `W(c) ≠ ⊥` exactly when the
`u_i` have a common eigenvector with eigenvalues `c i`. It also does not
state the formula `A_j(e_k) = z^{(j)}_k (Id + N^{(j)}_k)`, the
commutation or nilpotence of the `N^{(j)}_k`, their multivariable product
factorization, or the binomial expansion. Those remain separate
obligations of the whole-book program. The exponential-polynomial
coefficient statement of the same section is
`Langlands.CommutingTupleMatrixCoefficientExponentialPolynomialStatement`
in `Langlands.Representation.MatrixCoefficient.CommutingTupleStatement`,
and it does not depend on this file.

A proof is not part of this unit. Mathlib's
`Mathlib.LinearAlgebra.Eigenspace.Pi` contains the independence and
spanning theorems for commuting families with labels in the scalar field.
A proof would need to pass from complex labels to unit labels, and to
prove finite support and lattice invariance.

## Errata and imports

The supplementary source `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Its appendix corrections on PDF18–19 were reread for this unit. The only
entry for this passage (2010 p.322, l.-4) places parentheses around the
whole factor `z_k (Id + N_k)` before its integer power. It concerns the
later product formula, which the governing 2026 display already
parenthesizes, and does not affect the decomposition. The 2026 edition
governs the statement.

`Langlands.Representation.IntegerLattice` supplies the tuple subtype, the
lattice abbreviation and the representation `tupleRepresentationEquiv`.
`Mathlib.LinearAlgebra.Eigenspace.Basic` supplies
`Module.End.maxGenEigenspace`, and through its imports `iSupIndep`,
`Set.Finite` and `Set.BijOn`.
