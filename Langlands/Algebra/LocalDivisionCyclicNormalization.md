# Norm adjustment of a cyclic division-algebra parameter

Let `j` implement a generator `σ` of a degree-`d` unramified Galois subfield of the local division algebra. Multiplying `j` on the left by an embedded coefficient `t` preserves its conjugation on the field. The `n`-th power of the product has coefficient `t σ(t) ⋯ σ^(n−1)(t)`. At `d` this coefficient is the field norm, which multiplies the original central parameter.

The unramified norm theorem says that a field unit is a norm when its normalized order is a multiple of `d`. Therefore `normalizeImplementingUnit` constructs an implementing unit with any prescribed central parameter of the same normalized order modulo `d`. Its conjugation is unchanged, and the exact power equation is proved. This is the norm adjustment for the uniformizer power in Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), §2 B, printed p. 110. The unit construction takes the order congruence as a hypothesis.
