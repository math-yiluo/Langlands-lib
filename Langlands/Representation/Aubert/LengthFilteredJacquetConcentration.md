# Finite lifting of singleton-grade Jacquet concentration

This internal assembly removes the need to supply a finite Weyl-support chain
when applying the corrected support-filtration exactness theorems. Its inputs are
explicit conditional statements about the actual bundled quotient diagrams for
upper supports differing by a singleton. It does not prove those geometric
concentration inputs or signed effectivity.

The Lean proof uses `LengthOrderedSupports` to enumerate all coordinate Weyl
permutations in decreasing inversion length and form their finite prefix supports.
The initial support is empty and the final support is full. Each preceding prefix
is exactly the next prefix with its newly added permutation deleted. Both supports
are closed under strictly increasing inversion length, so the hypothesized graded
injectivity and exactness apply at every step.

The already constructed natural signed comparison between the actual associated
grades and the bundled support quotient diagrams transports those hypotheses to
the associated grades of the actual Jacquet complex. The existing finite filtered
injectivity and exactness lifts then give injectivity and middle exactness for the
actual Jacquet differentials. Thus the signs and genuine normalized quotient maps
are the same maps used by the support filtration, without substituting an abstract
complex for the actual one.

The defined predicate `UpperSingletonGradedConcentrationBelow` records exactly
the two lower concentration hypotheses for each upper singleton grade. The final
theorem packages these lower exactness conclusions together with an
explicit upper-degree zero hypothesis, using the existing degreewise actual
Jacquet equivalences. Its conclusion is precisely the existing
`JacquetConcentratedAt` condition. Neither this result nor the finite filtered
argument asserts exactness at the terminal homology degree.
