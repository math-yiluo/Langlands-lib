# Bernstein's binary rank induction from four analytic inputs

Authors: Worker 103; the analytic input statements are by Worker 105.

This internal reduction separates the rank induction from its four analytic
prerequisites. `BernsteinUnitaryInductionInputs F T` is precisely the conjunction
of the existing shifted highest-derivative irreducibility and unitarity
statement, lower shifted-derivative positivity, product positivity from the
factor bounds and unitary shifted top derivatives, and the unitary finite-length
irreducibility criterion. The package asserts no proof of those statements.

`bernsteinUnitaryProductIrreducibility_of_inductionInputs F T` proves the exact
published `BernsteinUnitaryProductIrreducibility F T` conditionally on this
package. In particular this file is not an unconditional proof of the task's
target. The field and carrier universes remain independent and the supplied
field topology is retained.

The proof first supplies unitarity of binary products of irreducible unitarizable
factors in all ranks. For positive ranks it applies the published normalized
product preservation theorem to the actual binary shape. For either rank zero
it replaces that irreducible factor by the actual binary unit, applies the
published unit equivalence, and transfers unitarity through the carrier lift
and rank pullback of the remaining factor.

It then inducts strongly on the sum of the two ambient ranks. Either zero rank
is covered by the separately proved binary boundary lemmas and the unitarity
argument above. For two positive ranks, choose a unitary additive character
using the published p-adic existence theorem and choose actual highest positive
derivative orders for both nonzero factors. The first analytic input makes
their shifted highest derivatives irreducible and unitarizable. Their total
rank is strictly smaller, so the induction hypothesis applies to their literal
binary product, including the possibility that one or both derivative ranks
vanish.

The actual `HighestProduct.shiftedHighestProductIso` transfers this
irreducibility and unitarity to the shifted derivative of the original product
at the sum of the two orders. Irreducibility implies its carrier is nonzero.
The published higher-vanishing theorem supplies vanishing above the sum, so the
sum defines an actual `GeneralLinearHighestDerivativeOrderData` for the
original product. The second and third analytic inputs give its lower
positivity. The factors have finite length by irreducibility, and the published
binary finite-length preservation theorem supplies finite length of their
product. The fourth analytic input then gives irreducibility of that product.

Finally, `bernsteinUnitaryProductIrreducibility_of_binary` passes from positive
binary ranks to every finite block shape and supplies the all-rank unitarity
clause, including the empty product.

The provenance is an internal composition of the explicit structural
isomorphisms and separate analytic statement interfaces. The four analytic
implications remain hypotheses, not accepted facts supplied by this file.
It implements the structural rank-induction route of Bernstein's Corollary
8.2(a), without importing the desired product irreducibility as an assumption.
