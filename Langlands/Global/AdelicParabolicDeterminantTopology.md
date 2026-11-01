# Continuous determinant multiplication on actual adelic induced sections

Author: Worker 2. Provenance: internal construction from the actual determinant
multiplication equivalences and the dedicated compact-open section spaces.
No new original-literature identification is made.

The number field and complex normed coefficient space have independent
universes. Every rank and ordered positive block shape is retained. A
finite-order Hecke character is required for the existing multiplier to preserve
the separate finite stabilizer and real-smooth archimedean slice conditions.
The source and target are the same actual covariant functions as in those
constructions, with the target Levi action twisted by the common block
determinant character.

`determinantEquiv` transports the existing actual linear multiplication
equivalence to the dedicated compact-open copies. Its forward and inverse
continuous-function evaluation formulas are exactly multiplication by
`χ(det x)` and its inverse unit.

A private general continuity lemma handles multiplication of a vector-valued
continuous function by one fixed continuous complex-valued function. On each
compact subset of the domain, the evaluation map is continuous. Currying the
pointwise scalar action proves continuity of the restricted multiplier.
Compact-open convergence is detected by these restrictions, giving continuity
on the full function space. This argument imposes no local compactness
hypothesis on the original domain.

The section topologies are induced by their faithful continuous-function
realizations. Composing the fixed-function multiplier with these realizations
proves `continuous_determinantEquiv` and
`continuous_determinantEquiv_symm`. Together with the existing algebraic
inverse laws they give `determinantMultiplier`, a continuous complex linear
equivalence. Its actual forward and inverse evaluation identities are exposed.

`determinantTwistEquiv` uses the same continuous multiplier as its underlying
linear equivalence and retains the established ambient-to-Levi representation
intertwining identity. `determinantMultiplier_rightAction` expresses it as the
actual right-translation covariance formula with scalar `χ(det g)`.
`determinantMultiplier_mapCLM` proves naturality for continuous coefficient
intertwiners: postcomposition before multiplying equals multiplication before
postcomposition by the same linear map, viewed between twisted Levi actions.
The proof uses faithful function realization and the coefficient map's complex
linearity; the second coefficient space has its own independent universe.

No completeness, finite dimension or continuity of the supplied Levi
representation is assumed. The topology controls function values on compact
sets; no derivative topology, jointly continuous group action, unitary
completion, nonzero section, Haar identification or automorphic existence
assertion is made.
