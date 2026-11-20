# Haar scaling of twisted conjugation through a vector filtration

Suppose a closed subgroup has a finite descending filtration by subgroups
stable under conjugation by a single ambient point, ending in the trivial
group. The continuous open vector quotient maps identify the next step as
a closed normal subgroup of the previous one. On each quotient the map
\(x\mapsto\alpha(x)^{-1}x\) acts by the linear displacement \(D=1-A\).

`displacementFiltrationFactor` forms the product of the inverse absolute
determinants of the successive invertible linear displacements.
`map_twistedConjugationMap_of_vectorFiltration` proves that this product is
the pushforward factor for any Haar measure on the initial subgroup. The
proof proceeds from the trivial last subgroup back up the filtration.
It uses the compact open cover inherited by each closed step and transports
its Haar calculation to the kernel lying inside the previous step. The
vector-quotient change of variables then supplies the next factor.

This internal measure calculation supports the comparison of actual compact
normalizations in Waldspurger's Lemma V.3.1.
