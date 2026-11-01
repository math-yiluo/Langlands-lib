# One common triangular basis on each actual generalized-weight block

Statement prepared by Worker 709; source and scope checked and explanation
expanded by Worker 308.

`Langlands.CommutingTupleGeneralizedWeightBlockBasisStatement` is a closed
Prop-valued definition with arbitrary carrier universe `u`. It states the
common triangular basis assertion for the actual block and generators
constructed in
`Langlands.Representation.IntegerLattice.GeneralizedWeightBlock`, which it
imports unchanged. This module states the assertion; it supplies no proof
of it.

## Mathematical statement

For every natural rank `d`, every finite-dimensional complex vector space
`V : Type u`, every actual commuting invertible tuple
`A : Langlands.IntegerLattice.CommutingInvertibleTuple d V`, and every tuple
of units `c : Fin d → ℂˣ`, let

```text
W = generalizedWeightBlock A c
  = ⋂ t : Fin d, maxGenEigenspace (A.1 t) (c t).
```

The operators are the imported constructions, all in the namespace
`Langlands.IntegerLattice`:

- `G_t = generalizedWeightBlockGenerator A c t`, the actual generator unit
  of the restricted lattice representation on `W`;
- `U_t = normalizedBlockGenerator A c t`, whose underlying endomorphism is
  `(c t : ℂ)⁻¹ • G_t`;
- `N_t = normalizedGeneratorDifference A c t = U_t - 1`, an actual
  endomorphism of `W`.

There exists one actual basis
`b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W` with all five properties
below. Row `i`, column `j` of the matrix of an endomorphism `T` means
`b.repr (T (b j)) i`.

1. For every `t`, `i` and `j`, if `j ≤ i`, then
   `b.repr (N_t (b j)) i = 0`. Thus the matrix of every `N_t` is strictly
   upper triangular: an entry may be nonzero only for `i < j`.
2. For every `t`, the underlying endomorphism of `G_t` equals
   `(c t : ℂ) • (1 + N_t)`.
3. For every `t`, `i` and `j`,

   ```text
   b.repr (G_t (b j)) i =
     (c t : ℂ) * ((if i = j then 1 else 0) + b.repr (N_t (b j)) i).
   ```

4. For every `t`, `i` and `j`, if `j < i`, then
   `b.repr (G_t (b j)) i = 0`.
5. For every `t` and `i`, `b.repr (G_t (b i)) i = (c t : ℂ)`.

The existential basis occurs before every generator and coordinate
quantifier, so the same basis works for the entire family. The second
property is the intrinsic normalization identity already proved by
`generalizedWeightBlockGenerator_eq_smul` in the imported construction.
It is included to identify the source's scalar-times-unipotent factors.
The last two properties explicitly state that each generator matrix is
upper triangular and has the prescribed scalar diagonal.

All mathematical inputs, including the typeclass instances, are bound
inside the proposition. The caller supplies no nilpotence, common basis,
flag, decomposition, factorization or support assertion. The only tuple
conditions are the invertibility and pairwise commutation in
`CommutingInvertibleTuple`.

## Source and derived formulation

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix C.III,
printed pp.279–280 / one-based PDF285–286, proof of the proposition.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`,
SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained file is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Both pages were read directly, and the formulas on PDF286 were visually
checked.

PDF285 introduces commuting invertible endomorphisms of a finite-dimensional
complex space and their actual integer-lattice representation. It describes
the common eigenvalue tuples and corresponding characters. PDF286 chooses
a common triangularization basis in which the representation matrices are
block diagonal, each block upper triangular with a scalar diagonal. For a
standard lattice generator, it writes

```text
A_j(e_k) = z_k^(j) (Id + N_k^(j)),
```

with all `N_k^(j)` strictly upper triangular.

This statement is derived from that passage. It expresses the source's
block assertion on the actual intersection of maximal generalized
eigenspaces, with the actual restricted lattice action, rather than on a
supplied matrix block. It uses basis coordinates in place of a matrix
object. The source's scalar `z_k^(j)` is the label `(c t : ℂ)` and its
normalized part is the imported difference `N_t`. The full coordinate
equation, explicit triangular vanishing and scalar diagonal are the
coordinate form of the source's displayed normalization. Indices use
zero-based `Fin` instead of the source's one-based indexing.

The separately registered supplementary errata for the 2010 edition,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
are retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
PDF18–19 were read, and the C.III correction on PDF19 was visually checked.
The correction to old p.322, line -4, puts the whole scalar-times-unipotent
factor under its later integer power. The 2026 PDF286 already has that
grouping. It changes none of the five equations in this statement.

## Scope and remaining obligations

Every natural `d` is included. For `d = 0`, the block is the whole space and
the conclusion still requires an actual basis; only the generator
conditions are vacuous. The zero vector space and zero blocks are included.
For a zero block, `Module.finrank ℂ W = 0`, so the basis is empty and all
coordinate conditions are vacuous. Labels range over all tuples of complex
units, including labels with zero block. No positive dimension, positive
rank, nonzero-block, diagonalizability or unitarity condition is imposed.

This is a source-facing statement about constructed blocks. The independent
`Langlands.CommutingNilpotentStrictUpperBasisStatement` instead concerns a
supplied commuting nilpotent family over an arbitrary field. A future proof
may use that result after proving nilpotence and commutation of the actual
differences. The present module neither assumes nor proves that generic
result, the generalized-weight decomposition, support identification,
multivariable factorization or the whole Appendix C.III proposition.

A proof of this exact proposition remains a separate obligation. Publishing
this statement does not prove the existence of its common basis.
