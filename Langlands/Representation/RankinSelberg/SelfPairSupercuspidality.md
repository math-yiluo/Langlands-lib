# Supercuspidality from the local Rankin–Selberg self-pair

`SupercuspidalOfSelfPairStatement` applies to a positive-rank generic
unitarizable representation over a p-adic field with its canonical topology.
Suppose its pair with its actual smooth contragredient has certified gamma
factor `G` and L-denominator `P`, for a nontrivial unitary additive character
and a self-dual measure. If the meromorphic function given by `G` has positive
order on the real axis only at zero, and `P` has a simple root at one, then
the representation is supercuspidal. The polynomial condition is the simple
L-pole at `s = 0` in the variable `X = q^(-s)`.

The proof uses the Library's local self-pair gamma rigidity to express the
original action as a normalized product of unitarizable supercuspidal blocks.
This step uses the centered segment argument of Henniart (2000), Appendix
A.1–A.3, printed pp. 453–454 (PDF pp. 15–16).

For such a product, normalized induction duality realizes the actual smooth
contragredient as the product of the block smooth contragredients. Unitarity
passes to each block dual via the Hermitian form. The blocks and their duals
are square-integrable, so the tempered pair formula of Jacquet–Piatetski-Shapiro–Shalika
(1983), Proposition (8.4), printed pp. 451–452 (PDF pp. 86–87), writes the
certified denominator as the product over all ordered block pairs.
Each diagonal pair contributes one to the root multiplicity at one, by
Proposition (8.1)(ii), printed p. 443 (PDF p. 78), and admissible biduality.
The root multiplicities add, giving the number of blocks as a lower bound
for the order of the self-pair pole.

A positive-rank block shape has at least one block, so a simple pole forces
exactly one. The one-block normalized induction equivalence identifies the
original action with that supercuspidal block, reindexed to its original
rank. The criterion combines the cited local results and leaves the gamma
and L-pole hypotheses as inputs.
