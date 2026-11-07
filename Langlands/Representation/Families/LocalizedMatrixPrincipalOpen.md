# Principal polynomial neighborhoods from localized coefficient matrices

Worker 1444. This derived construction assembles the determinant and
polynomial-coordinate steps for a coefficient matrix family defined
after one localization. It supplies no representation-theoretic
finiteness or detection theorem.

Let `B` be a commutative complex algebra, `g : B`, and `S` any
localization of `B` away from `g`. The complex scalar action on `S`
extends that on `B`. No domain assumption on `B` or `S` is made.
`awayEvaluation` extends a complex character of `B` to `S` whenever
the character is nonzero at `g`. The extension agrees with the
original character on `B`.

Mathlib's localization section represents every `z : S` by a regular
numerator and a power of `g` as denominator. `localizedNumerator`
selects that numerator. Applying `awayEvaluation` to the clearing
identity proves that nonvanishing of this numerator is equivalent
to nonvanishing of the localized element wherever the evaluation is
defined.

`regularWitness g z` multiplies the numerator by `g`. Its
nonvanishing therefore ensures both that evaluation on `S` is
defined and that the evaluated element `z` is nonzero. This retains
the original localization domain rather than extending a matrix
condition beyond its domain of definition.

For any family of finite matrices over `S`, irreducibility at a
character where `g` is nonzero gives a determinant witness in `S`
equal to one at that character, by the imported
`MatrixGenerationWitness.exists_principal_neighborhood`.
`exists_regular_principal_neighborhood` applies the preceding
numerator construction to this witness. It produces `f : B`,
nonzero at the original character, whose nonvanishing gives
irreducible specialized matrices and a valid localization
evaluation. The irreducibility predicate is the published common
invariant-subspace predicate, including its zero-dimensional
convention.

For actual unramified characters of a connected reductive group
over a nonarchimedean local field, an algebra equivalence `e`
identifies `B` with the published regular-function algebra.
`coefficientCharacter` evaluates through this equivalence, so `B`
may also be the algebra on a literal Levi transported by an existing
comparison. The point topology is canonical. As in the imported
coordinate comparison, affine and locally-finite-type instances
are exposed; connected reductivity supplies both.

`exists_polynomial_principal_neighborhood` applies
`UnramifiedPolynomialWitness.rationalRegularPolynomial` to `e f`.
Its principal open set in the published finite coordinates is
exactly the nonzero locus of `e f`. Thus the polynomial open set
contains the original character, remains inside the localization
domain and certifies irreducibility of the specialized matrices.
The field, coefficient, localization, generator and matrix-index
universes are independent. Rank zero and empty matrix index types
are included.

The provenance is the two imported internal witness constructions
and Mathlib's universal property and numerator section for a
principal localization. It implements the algebraic part of
Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026 version, VI.8.4 Proposition proof, printed pp.192–193 /
PDF pp.198–199, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
In that proof a coefficient localization makes the fixed-vector
module free. This module assumes that the matrices and the algebra
equivalence have already been constructed. It does not produce a
local basis, compare them with an induced family, establish
admissibility, or construct a compact subgroup detecting all
irreducible subquotients. In particular it does not prove
`InducedIrreducibilityOpenStatement`.
