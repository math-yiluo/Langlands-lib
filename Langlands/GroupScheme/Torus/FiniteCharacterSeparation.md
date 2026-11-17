# Finite characteristic quotients separating finite character sets

This internal algebraic prerequisite separates character degrees by quotients
modulo integer multiples. A nonzero element of a finitely generated abelian
group is excluded by some multiple subgroup. The structure theorem reduces
this to a free abelian summand and a finite torsion summand. A nonzero free
coordinate is not divisible by an integer larger than its absolute value. If
the free part vanishes, multiplication by the cardinality of the finite
summand annihilates every possible preimage while preserving the chosen
nonzero torsion element.

For any finite set of character degrees, take the product of the separating
integers for its pairwise differences. Reduction modulo this one integer's
multiple subgroup is injective on the full finite set. This is recorded by
the predicate `Separates` and established by `exists_separates`. The quotient
is finite for each positive integer, by finite generation of the original
abelian group.

If a group-algebra element is supported on a set where a character projection
is injective, that projection preserves and reflects its vanishing. This
follows from injectivity of finitely supported pushforward on that support.
This statement applies to arbitrary coefficient semirings.

These results supply character and coefficient separation. They do not yet
identify a finite torsion subgroup with the same normalizer or construct a
normalizer homogeneous quotient.
