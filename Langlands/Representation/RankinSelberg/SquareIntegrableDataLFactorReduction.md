# Reduction of the square-integrable-data L-factor formula

Authors: Worker 1748 and Worker 1753.

This internal module reduces the unchanged
`SquareIntegrableDataLFactorStatement.{uF, uV, uW}` to explicit equal-exponent
grouping, tempered and Langlands-type product formulas, and regular
Langlands-data uniqueness. The three carrier universes remain arbitrary and
independent. The analytic formulas are used at the maximum of each original
block universe with the field universe.

`squareIntegrableDataLFactor_of_grouping` first lifts the original essentially
square-integrable blocks to these maximum universes. Their normalized
inductions are actually equivalent to the original inductions, so they have
the same specified irreducible quotients. The supplied grouping assertions
give tempered data and actual isomorphisms from the lifted inductions to their
standard modules. Transporting the quotient witnesses along these isomorphisms
gives tempered presentations of the original representations.

The grouped-product theorem supplies a polynomial `P`, all the lifted
block-pair polynomials `Q`, and their double-product equality. The imported
`isLanglandsPairLPolynomial_of_saturatedData` certifies this exact `P` through
all tempered presentations in the original universes, using the two explicit
regular-data uniqueness premises. Each `Q` certifies the original blocks by
transport along the two block universe-lift equivalences. Neither the
polynomials nor their index types change, so the same double-product equality
finishes the result.

`squareIntegrableDataLFactorPolynomials` packages a chosen pair `(P, Q)` with
these certificates and their equality. The choice is made from the preceding
existence theorem. `squareIntegrableDataLFactor_of_prerequisites` universally
quantifies the same argument to conclude the exact existing proposition.

The provenance is internal: the module assembles the imported actual-carrier
transport, grouped-product computation, and fixed-polynomial certificate
reduction. Worker 1753 authored the reused fixed-polynomial certificate
reduction with Worker 1748's carrier adapters. This module supplies no closed
proof of the analytic formulas, grouping, or regular-data uniqueness, and
therefore does not by itself close the unconditional host proof task.
