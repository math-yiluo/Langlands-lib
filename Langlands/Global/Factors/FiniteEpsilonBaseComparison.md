# The finite epsilon bases from two completed functional equations

Two `RelativeWeilEngine.HasGlobalEquation` packages have the same conductor base if both forward and dual finite Euler products have common values on a right half-plane, the archimedean products have matching real-Gamma counts, and the archimedean epsilon products differ by a constant complex unit. The finite epsilon products are supplied in the form `c · M^(-z)` with positive `M`. The conclusion is equality of the positive bases. `prod_epsilonMonomial_eq` supplies the required form for a finite product of actual epsilon monomials, with `M` the product of the local residue-cardinality powers.

This is an internal reduction of the comparison in Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula* (1989), Chapter 1, §6, equations (6.15)–(6.17), printed pp. 69–70. The `HasGlobalEquation` interface supports multiplying the equations on one side and grouping the places in a finite extension.

The Lean proof uses uniqueness of both Euler-product limits and meromorphic continuation to identify both finite L-functions as punctured germs. It cross-multiplies the completed equations and cancels the common finite L-function using its nonvanishing germ. After cancellation the four archimedean L-products satisfy the hypothesis of `archimedeanGammaExponentComparison` with base `M_A / M_B`. The resulting quotient is one.

`CuspidalPairEpsilonComparisonData` provides the adapter from the completed cuspidal pair equation when its finite factors are nonzero on a right half-plane. It also proves the Gamma counts and the dependence on the additive-character scale for the supplied real and complex pair presentations.
