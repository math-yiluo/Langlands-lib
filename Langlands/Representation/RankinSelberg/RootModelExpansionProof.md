# Proof of the coefficient-model root expansion

`Langlands.RankinSelberg.equalRankRootExpansion` proves
`EqualRankRootExpansionStatement F T n` with independent field and
representation-space universes.

First the proof extracts the two finite sets `X` and `Y` supplied by the
assumed coefficient torus expansions. The root-product theorem gives the
finite-function family on their product index type, with each function the
product of the two cumulative-coordinate pullbacks and the inverse modulus.
An equivalence with `Fin (Fintype.card I)` enumerates this family. This choice
is made before any functional, coefficient, row test or matrix is introduced.

For arbitrary such data, apply the two coefficient expansions to
`modelRepresentation π ℓ k f` and `modelRepresentation σ ℓ' k f'`. The
underlying functions of these actual model elements are definitionally
`g ↦ f(g*k)` and `g ↦ f'(g*k)`. Thus the resulting diagonal expansions
are exactly the two translated coefficients in the target. The proof
rewrites the finite-set sums as sums over membership subtypes.

The root-product theorem now supplies Schwartz–Bruhat functions on the full
field coordinate space for the product of those two expansions, the row
test and the inverse modulus. Substituting the coefficient equalities and
reindexing the final sum by the chosen equivalence gives the required
identity.

This internal proof only combines the given expansions with the model action
and the pointwise product reduction. It retains zero functionals, empty
families, every invertible right translate and rank one. It proves no
unconditional Whittaker expansion, integral formula or analytic conclusion.
