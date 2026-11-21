# Distinguished standard epsilon comparison from completed Hecke twists

`StandardTwistDistinguishedEpsilonStatement` concerns actual determinant twists
of a cuspidal representation over `K` and a cuspidal representation over `L`,
with compact adelic additive quotients over both fields. The family of twists
has cardinality `[L : K]`, and the given finite place `v₀` has one place `w₀`
above it. The second representation in every pair is the rank-one constant
representation. Supply the actual contragredient presentations with
irreducible admissible finite components in all forward and dual presentations.
The lower dual presentations are the inverse Hecke twists of the given lower
contragredient. `CuspidalPairGlobalFunctionalEquationStatement` is a premise.

For the supplied presentations, the local hypotheses give the two lower
polynomial identities at `v₀`, separation of the upper forward and reflected
dual roots at `w₀`, and the comparison of the finite Euler factors and positive
epsilon bases at each other place. These conditions apply to each choice of
actual finite factors. Choose the completed equations for the Hecke twists and
the upper representation with the standard additive characters. The distinguished
Euler comparison forces both upper polynomials at `w₀` to be one. The forward and
dual finite Euler factors then match at every place. Comparing the Gamma counts
and cancelling the auxiliary positive epsilon bases yields the distinguished
monomial comparison for the chosen finite factors at every spectral parameter
up to one constant complex unit.

This is an internal assembly of the analytic comparison in Arthur–Clozel,
Chapter 1, proof of Proposition 6.9(ii), printed p. 70 (PDF p. 84). The result
uses completed equations (6.15) and (6.16) to compare the exponents in (6.17).
