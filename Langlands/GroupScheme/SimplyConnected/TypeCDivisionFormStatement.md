# Division-algebra presentations and indices of simply connected type-C groups

Authors: Worker 178, Worker 64.

`Langlands.GroupScheme.TypeCDivisionFormStatement.{u}` is an unproved
prerequisite for identifying forms of type C. It quantifies over every field
`K : Type u`, every affine locally finite type group scheme `G` over `Spec K`,
actual `d : TitsIndexData G`, an absolute rank `n ≥ 2`, and a numbering
`e : d.Vertex ≃ Fin n` matching every actual Cartan entry to `CartanMatrix.C n`.
It assumes that `G` is simply connected and absolutely almost simple.
There is no supplied algebra, involution, form, or group presentation.

The conclusion constructs positive integers `degree` and `m`, a central
finite-dimensional division algebra `D : Type u`, an involution of the first
kind `σ`, and an invertible trace-valued antihermitian matrix `H` of size `m`.
They satisfy

- `m * degree = 2 * n` and `dim_K D = degree^2`;
- `dim_K σ.symmetricSubspace = degree * (degree + 1) / 2`;
- `σ.wittIndex H = splitRank G`;
- `Nonempty (G ≅ σ.symplecticGroup H)`;
- a simple vertex `a` is distinguished exactly when its one-based number
  `(e a).val + 1` is `j * degree` for some `1 ≤ j ≤ splitRank G`.

`NeZero m` is included to form the reduced norm in the model. The natural Witt index and the integer bound on `j` are cast to `ℕ∞`
when compared with the Library split rank. The degree is
explicitly positive; positive matrix size also follows from its product
formula. The assertion covers arbitrary split rank, including zero, and
arbitrary absolute rank at least two. It has no local-field assumption and no
characteristic restriction. The involution and form use the published left
row-vector conventions of `Quaternionic.Forms`.

The condition `σ.IsAntihermitian H` includes trace-valued diagonal entries,
not just the conjugate-transpose identity. This matters in characteristic two.
The actual model is the reduced-norm-one subgroup of the unitary isometry
scheme on all test schemes, as defined in `Quaternionic.GroupSchemes`.
The conclusion concerns the given simply connected group scheme over `K`.

## Original source and derived formulation

J. Tits, *Classification of algebraic semisimple groups* (1966), Table II
explanations, printed pp.54–55 / PDF pp.59–60, and the type-C entry, printed
p.56 / PDF p.61, give the division degree, matrix size `2n/degree`, symmetric
subspace dimension, antihermitian form of index `r`, and distinguished
vertices `degree, 2*degree, ..., r*degree`. Source ID:
`tits-1966-classification-algebraic-semisimple`; proceedings PDF SHA-256:
`962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.
The original pages were read and the type-C table was inspected as an image.
Its special-field rows are not used here.

This is a derived scheme-level formulation, with additional proof obligations.
Tits describes a representative of each strict isogeny class by rational
points. A proof must construct the division algebra, involution and
trace-valued form, identify the original simply connected scheme with the
published reduced-norm-one model, and compare the actual root restrictions
with the displayed distinguished vertices under the supplied Cartan numbering.
It must prove the split-rank/Witt-index comparison and the characteristic-two
trace condition, rather than infer scheme equality from a rational-points
bijection. The source also lists restrictions on which degrees and indices
occur; this proposition asserts only the listed consequences needed by its
consumer and does not assert a converse existence theorem.

For the rank-one consumer, `splitRank G = 1` and distinguished vertex 2
force `degree = 2`. The degree formula then gives `m = n`, the algebra has
dimension four, and the symmetric subspace has dimension three. That extraction
is separate from this unproved general classification statement.
