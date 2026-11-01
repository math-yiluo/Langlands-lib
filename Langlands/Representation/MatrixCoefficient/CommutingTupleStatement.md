# Exponential-polynomial coefficients of commuting invertible tuples

Author: Worker 709.

`Langlands.CommutingTupleMatrixCoefficientExponentialPolynomialStatement.{u}`
is a closed Prop-valued definition. It states the tuple formulation of the
coefficient proposition in David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix C.III,
printed pp.279–280, one-based PDF285–286. Both pages were read directly.
The original source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

## Objects, coefficient and quantifiers

For each natural `d`, the carrier `V : Type u` is an arbitrary
finite-dimensional complex vector space. The parameter
`A : Langlands.IntegerLattice.CommutingInvertibleTuple d V` uses the
published construction in `Langlands.Representation.IntegerLattice`. Its
entries `A.1 i` are actual units of `Module.End ℂ V`, and its subtype proof
asserts pairwise commutation. Thus each entry includes its two-sided
inverse. No representation realizing this tuple is an additional premise.

For a fixed vector `v` and algebraic complex-linear functional `ell`, the
left side is `ell` applied to the action on `v` of the actual finite product
of the units `A.1 i ^ n i`. Each exponent has type `ℤ`; negative exponents
use the stored inverses. `Finset.univ.noncommProd` uses the proof
`(A.2 hij).zpow_zpow _ _` that powers of distinct entries commute. The
result is a unit, coerced to its underlying linear endomorphism before it
acts on `v`. Multiplication of endomorphisms is composition, with the
rightmost factor acting first. Commutation makes the finite product
independent of enumeration, agreeing with Renard's displayed composition.
The coordinate type `Fin d` shifts the source's one-based indexing by one.

For every such tuple, vector and functional, the statement selects a
natural `l`, characters
`χ : Fin l → Langlands.IntegerLattice.Lattice d →* ℂˣ` and polynomials
`Q : Fin l → MvPolynomial (Fin d) ℂ`. Here
`IntegerLattice.Lattice d` abbreviates
`Multiplicative (Fin d → ℤ)`: its multiplication is addition of integer
coordinates. The characters take values in all complex units, so the
statement imposes no unitarity condition. Each polynomial is ordinary,
with natural exponents; it is evaluated at the canonical complex casts
of the integer coordinates.

These three witnesses precede `∀ n : Fin d → ℤ`. One finite family
therefore gives the coefficient expansion on the entire lattice,
including every negative coordinate and every mixture of signs. The
coefficient uses the product at `n`, without replacing it by an inverse
action or applying complex conjugation. The proposition requires neither
distinct characters nor a degree bound.

All natural `d` are allowed. At `d = 0`, the left side uses the empty
product, hence the identity action, and the polynomial ring has no
variables. The carrier may be the zero vector space; the coefficient and
the finite family may also be zero. No nontriviality, positivity,
topology, smoothness, diagonalizability, basis choice, generalized-weight
decomposition or assumed coefficient expansion enters the premises.

## Relation to existing statements and retained obligations

This statement reuses the existing commuting-tuple object. It does not
duplicate the tuple-to-representation equivalence.
`Langlands.IntegerLattice.tupleRepresentationEquiv_apply_apply` identifies
its explicit product action with the representation
`Langlands.IntegerLattice.tupleRepresentationEquiv d V A` at
`Multiplicative.ofAdd n`.

The existing
`Langlands.IntegerLatticeMatrixCoefficientExponentialPolynomialStatement`
in `Langlands.Representation.MatrixCoefficient.IntegerLatticeStatement`
has a representation as its input. Its proof,
`Langlands.integerLatticeMatrixCoefficientExponentialPolynomial` in
`Langlands.Representation.MatrixCoefficient.IntegerLatticeProof`, proves
that representation formulation. The present target makes the supplied
tuple and the actual product explicit. A separate proof can apply that
theorem to the constructed representation and use the published product
formula. This module imports neither that proof nor a hypothetical
tuple-coefficient realization.

The source first identifies a commuting tuple with its lattice action,
defines its coefficient, and states the expansion on printed p.279.
The direct product formulation here combines those consecutive source
formulas. The source proof on p.280 uses simultaneous triangular blocks
and nilpotent binomial expansions. This statement does not construct those
intermediate objects or prove their separate assertions. It also supplies
no proof of its own proposition.

## Errata and imports

The supplementary source `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Its appendix corrections on PDF18–19 were checked; PDF19 was reread for
this target. The final correction puts parentheses around the entire
scalar-times-unipotent factor before its integer power. The governing
2026 display already contains those parentheses, and the correction
changes neither the tuple action nor the coefficient proposition.
No `notes/errata` directory was present in the inspected workspace.
The older errata supplement the source comparison; the 2026 edition
governs the target.

`Langlands.Representation.IntegerLattice` supplies the tuple subtype,
lattice abbreviation, complex vector-space and finite-dimensionality
interfaces, and finite commuting product API.
`Mathlib.Algebra.MvPolynomial.Eval` supplies ordinary multivariable
polynomials and their evaluation. Every object in the statement is
therefore an existing concrete construction.
