# Proof of exponential-polynomial coefficients for commuting invertible tuples

Author: Worker 709. Submitted by Worker 277, who recompiled the unchanged
Lean file and reread the cited source pages.

`Langlands.commutingTupleMatrixCoefficientExponentialPolynomial.{u}` proves
the exact published proposition
`Langlands.CommutingTupleMatrixCoefficientExponentialPolynomialStatement.{u}`
from `Langlands.Representation.MatrixCoefficient.CommutingTupleStatement`.
The statement and its imported files are unchanged.

## Implemented proof

For a natural `d`, a finite-dimensional complex vector space `V : Type u`,
a supplied commuting invertible tuple `A`, a vector `v` and an algebraic
functional `ell`, use the actual representation
`Langlands.IntegerLattice.tupleRepresentationEquiv d V A`.
The published theorem
`Langlands.integerLatticeMatrixCoefficientExponentialPolynomial` applies
to this representation and returns a natural `l`, complex-unit-valued
lattice characters `χ` and ordinary multivariate polynomials `Q`.

The proof returns these same three witnesses before introducing the
arbitrary integer tuple `n`. Unfolding `Langlands.matrixCoefficient`
identifies the representation coefficient with
`ell (tupleRepresentationEquiv d V A (Multiplicative.ofAdd n) v)`.
The published equality
`Langlands.IntegerLattice.tupleRepresentationEquiv_apply_apply` rewrites
this action as the actual `Finset.univ.noncommProd` of the units
`A.1 i ^ n i`, coerced to its underlying endomorphism and applied to `v`.
The integer coordinates are definitionally the additive coordinates of
`Multiplicative.ofAdd n`. This is precisely the left side of the target.
The right side and all finite witnesses are unchanged.

The theorem retains the target's arbitrary carrier universe and every
integer exponent, including negative and mixed-sign coordinates. It adds
no hypothesis. In particular, `d = 0`, the zero vector space and zero
coefficients remain included. The characters take values in all complex
units, with no unitarity requirement; the polynomials have ordinary
nonnegative monomial exponents and are evaluated at complex casts of the
integer coordinates. No distinctness, degree bound or representation
realization premise is added.

## Source correspondence and reuse

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix C.III,
printed pp.279–280, one-based PDF285–286. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Both pages were read directly during preparation of the target.
The opening tuple action and the following coefficient proposition give
the target's explicit product formulation.

This proof is an adapter from the published representation-form theorem
by Worker 219 and the published tuple-to-representation construction. It
imports them by Lean name. The representation-form proof proceeds by
induction on the number of coordinates and single-operator generalized
eigenspaces, as described in its paired Markdown. This adapter neither
copies that proof nor constructs a simultaneous generalized-weight
decomposition or common triangular basis. Renard uses those intermediate
objects in his source proof; their independent assertions remain separate
formalization obligations.

The target Markdown records the supplementary 2010 errata check:
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19, especially the final parenthesis correction on PDF19. The
governing 2026 display already includes that grouping. This adapter uses
the actual integer powers of the entire supplied invertible operators
and does not use the scalar-times-unipotent display.

The only imports are the unchanged tuple statement and the published
representation-form proof. The former supplies the tuple construction
and product-action equality; the latter supplies the expansion theorem
and, through its imported statement, the matrix-coefficient definition. The resulting theorem proves this
coefficient target only, without claiming completion of Appendix C.III
or the whole book.
