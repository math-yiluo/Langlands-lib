# Compact change for the density package and unitary orbit weight

Fix a torus morphism and cocharacter in a connected reductive group over a
nonarchimedean local field, and a density package `P` for a smooth complex
representation of the literal Levi. The field and representation carrier have
independent universes. `DensityPackage.changeCompact` takes a compact open
subgroup `L` with both parabolic–compact products and produces a package whose
compact is `L`. The convergence subsets and the generic irreducibility locus
are inherited from `P`. The product factorizations at `L` give the new compact
models.

The construction uses `DynamicOppositeCompactChange` for the two
continuations and the formula for the canonical scalar. Inverting that
formula multiplies the old inverse by the constant inverse of the forward
and reverse quotient Haar product. A constant is regular at each unitary
character, so the product gives the regularity field of the new package.

For a split torus, the proved finiteness of the rank-one gamma products
makes both density constants strictly positive. `compactDensityScale` divides
the new density constant by the product of the old density constant and the
two quotient Haar factors. The comparison of inverse values and
`plancherelWeight_eq` show that the new weight is the old weight multiplied
by this positive real scale. The proof uses regular evaluation and multiplies
through by the positive constants, so the equality holds also at zeros of the
weight.

For a square-integrable inducing representation, the same equality holds on
the actual discrete-series orbit by surjectivity of its unitary character map.
Both sides use the same representation and central-quotient Haar measure.
This is a derived comparison of the Library's density expressions. It supplies
the upper-weight change to the common compact in the weak-term step of
Waldspurger VI.3.1.
