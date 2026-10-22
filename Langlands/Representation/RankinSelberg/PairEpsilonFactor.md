# Conditional epsilon factors of a pair

Worker 31. This module in `Langlands.RankinSelberg` constructs the epsilon
monomial from an existence proof for the published `IsPairEpsilonFactor`
relation. It returns a nonzero rational function in `X = q^{-s}`, packaged
as a unit, and separately supplies its nonzero complex monomial value at
each `s`. It proves choice uniqueness and invariance under representation
equivalence. It does not prove the analytic existence theorem.

## Source and provenance

Jacquet--Piatetski-Shapiro--Shalika, *Rankin--Selberg convolutions* (1983),
Theorem 2.7(iii), printed page 391, gives the epsilon factor in the form
`c q^{-ms}` in the equal- and unequal-rank functional equations, with one
factor for all unequal-rank blocks. The published `EpsilonFactor` module
formalizes that property as `IsPairEpsilonFactor`.

This module is derived formal packaging: it chooses a witness of that
exact relation, proves that it is the unique witness when `q > 1`, and
forms the specified monomial using units. The relation's original-source
conventions are preserved. In particular the central-character sign in
JPSS's functional equation is separate from the epsilon monomial.
The shared `IsSelfDual psi nu` hypothesis is a required input to the
factor constructors, retaining the Fourier normalization described in
the notation section of JPSS, printed page 378.

## Parameters

The field `F : Type uF` has field, valuative relation, topology,
nonarchimedean-local-field and measurable structures. The representations
are complex linear, with arbitrary carrier universes `uV` and `uW`:
`pi` acts on `GL_(r+1)(F)` and `sigma` on `GL_(n+1)(F)`.
The smaller general linear group and upper unipotent subgroup have Borel
structures, and their left quotient has a measurable structure.
These are the parameters of the published epsilon relation.

The factor constructors additionally require a Borel structure on `F`,
Hausdorffness and total disconnectedness, as needed by
`IsSelfDual psi nu`. Local compactness and the topological ring
structure come from the local-field instance.
`q : Nat` and the absolute value `abv` remain explicit parameters;
a p-adic application supplies the residue cardinality and normalized
absolute value. The self-duality proof is required by the API but does
not enter the algebraic monomial computation.

Rank one is `n = 0`. The inherited relation dispatches to equal rank
when `r = n` and unequal rank when `n < r`. Its branch when `r < n`
is false, so no existence proof can be supplied in that branch.
Rank exchange is a separate interface obligation.

## Rational monomial

`rationalEpsilonMonomial c m : RationalFunctionsˣ` is `c X^m` for
`c : Complexˣ` and `m : Int`. It maps the constant unit into the
rational function field and multiplies by the integer power of the
nonzero unit `X`. The unit operations supply all inverse and
nonvanishing proofs.
`coe_rationalEpsilonMonomial` gives its exact rational-function value.
This helper does not depend on a representation, field or measure.

## Existence and choice

`PairEpsilonFactorExists q psi abv nu pi sigma` is the proposition
that some `(c,m) : Complexˣ × Int` satisfies `IsPairEpsilonFactor`.
The witness therefore has the actual JPSS functional-equation property,
including the nonvacuity requirements: a compatible quotient measure
exists, both representations have nonzero Whittaker functionals, and
the equation holds for every compatible measure and every pair of
nonzero functionals. Nothing is replaced by an unconstrained
coefficient or exponent.

`pairEpsilonData h` chooses a witness from that existence proof.
`pairEpsilonData_spec` proves its defining relation.
`pairEpsilonData_eq` identifies it with any other witness for `q > 1`,
using the published `IsPairEpsilonFactor.unique`.

`PairEpsilonFactorExists.of_equiv` transports existence along actual
representation equivalences, using the published invariance of the
relation. `pairEpsilonData_congr_equiv` proves equality of the chosen
data for equivalent representations when `q > 1`. The carrier
universes may change.

## Factors and spectral values

`pairEpsilonFactor hnu h` applies `rationalEpsilonMonomial` to
`pairEpsilonData h`. Its coercion lemma states the formula
`C(c) X^m`.
`pairEpsilonFactor_eq` identifies it with the monomial of any witness,
and `pairEpsilonFactor_congr_equiv` proves invariance under actual
representation equivalences. Both use `q > 1`.
Different proofs of the same existence proposition give the same
constructor by Lean proof irrelevance.

`pairEpsilonValue hq hnu h s : Complexˣ` is the nonzero value
`epsilonMonomial q c m s`, with `(c,m) = pairEpsilonData h`.
The already proved `epsilonMonomial_ne_zero` supplies the unit proof;
`hq : 1 < q` supplies its positivity hypothesis. Its coercion lemma
is definitional.

A theorem equating this spectral value with Mathlib's evaluation of
the rational factor is not supplied here. The two explicit formulas
are proved individually. No claims about gamma factors, analytic
existence, twists, additive-character change, rank exchange or
nongeneric Langlands data are made by this module; those are separate
obligations of the broader construction task.
