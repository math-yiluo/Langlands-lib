# A common-denominator Laurent quotient

Author: Worker 36.

The namespace `Langlands.Analytic.LaurentPresentation` constructs an
actual unit-radius quotient from a presented strict affinoid base
A = K⟨X₁,…,Xₙ⟩ / closure(span S). The functions f_i and g_j are chosen
Tate-series representatives for upper and lower inequalities.

`denominator` is G = product_j g_j, and `complementaryProduct j` is the
product G_j over indices other than j. The proved identity
`mul_complementaryProduct` says g_j G_j = G. The tuple `numerators`
consists, in order, of f_i G, the G_j, and one additional numerator 1.
The three numerator evaluation lemmas identify the corresponding finite
indices. These algebraic definitions and lemmas need only an ultrametric
normed coefficient field.

For complete K, `algebra` specializes the constructed rational quotient
to that denominator and tuple. Thus it is the quotient of a single
enlarged Tate algebra by the closure of the old relations and the
relations G Y_a minus the corresponding numerator. `baseMap` is the
actual bounded map induced from the base quotient. Neither a spectrum
realization nor a factorization property is assumed in these definitions.
`locus` is the set of base spectrum points satisfying x(f_i) ≤ 1 and
1 ≤ x(g_j), with each representative projected to A before evaluation.
Both tuples may be empty; an empty product is 1. Zero quotients are allowed.

This is derived presentation-level infrastructure for Berkovich's
*Non-archimedean analytic spaces* (Trieste 2009), Exercise 2.2.2(i),(iii),
p.9: the source gives Laurent domains and says they are rational.
Here the common-denominator construction includes a redundant numerator
1 to make the unit-ideal condition automatic. It is a specific rational
quotient, not a claimed definitional equality or proved isomorphism
with the source's relative-series quotient by T_i−f_i and g_j S_j−1.
The target in `Statement` addresses its spectrum locus. The source's
arbitrary positive radii, full analytic-domain factorization property
of Definition 2.2.1, and independence of presentations remain separate.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
