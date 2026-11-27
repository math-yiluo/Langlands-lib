# Comparing finite pair denominators at the distinguished completion

`completedPairDistinguishedPolynomialComparison` proves
`CompletedPairDistinguishedPolynomialComparisonStatement`. It compares a finite
family of lower completed cuspidal pair equations with one upper equation over
an extension of number fields with compact adelic quotients. The finite factors
come from `FinitePairFactorChoice` for actual cuspidal presentations of two
arbitrary positive ranks in the standard global additive normalization. A
distinguished finite place has a unique upper place of residue cardinality
`q^f`, where `q` is the lower residue cardinality. At each other finite place
the product of the lower forward factors agrees with the product of the upper
forward factors over its fiber. The same hypothesis applies to the dual factors.

Given the completed equations and open-unit-disk nonvanishing of all
forward and dual distinguished denominators, the theorem shows that the upper
forward denominator composed with `X^f` equals the product of the lower forward
denominators. The hypotheses permit nonconstant distinguished denominators
throughout.

The proof first enlarges the lower epsilon sets to their union, using the
supplied triviality of each epsilon datum outside its original set. It then
multiplies the lower equations and concatenates their archimedean Gamma lists.
The finite-place products have nonzero limits on right half-planes. Grouping the
upper product by its lower places and multiplying both products by their
respective distinguished denominators leaves equal pointwise product families,
for both the forward factors and the dual factors. This uses the singleton
fiber at the distinguished place and the identity
`q^(-f z) = (q^(-z))^f`.

The certified denominators have constant coefficient one. The residue
cardinalities force `f > 0`, so the substitution `x ↦ x^f` preserves the open
unit disk. The standard reflection lemma then gives disjoint forward and
reflected dual roots in the common variable. The two epsilon multipliers are
products of nonvanishing analytic monomials and nonzero constants. Applying
[`distinguishedPairEulerFromEquations`](DistinguishedPairEulerComparison.md)
to the grouped equations identifies the forward polynomials.

This assembles the finite-product and residue-variable steps in Henniart and
Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique
non nulle* (2011), II.6.19, equations (3)–(5), printed pp. 133–134
(PDF pp. 141–142). The retained copy is registered as
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
The completed equations, comparisons at the other finite places, and local
root bounds are explicit premises of the Lean statement.
