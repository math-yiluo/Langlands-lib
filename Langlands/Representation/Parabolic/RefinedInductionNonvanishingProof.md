# Refined induction evaluation and nonvanishing

`Langlands.Parabolic.normalizedRefinedInductionNonvanishing` proves the exact
public `NormalizedRefinedInductionNonvanishingStatement`, preserving independent
field and inducing-carrier universes and all natural ranks.

The proof installs the supplied p-adic topology, the existing product-Levi
topological-group structure, and its proved nonarchimedean and locally compact
structures. The refined Levi projection is continuous, so smoothness of the
input pulls back to the parabolic. The positive half-modulus has open kernel;
the public smooth-twist theorem therefore makes the actual inflated and twisted
inducing action smooth.

For each vector `v`, `Induction.compactLocalSection` at the identity and with
quotient neighborhood `Set.univ` supplies a compactly supported section. Its
underlying value is a member of the existing smooth induced carrier, and
`compactLocalSection_apply` gives evaluation equal to `v`. This proves
surjectivity of the statement's actual evaluation map. Surjectivity onto a
nontrivial carrier then implies nontriviality of that same induced carrier.

This is an internal specialization of published constructions. It needs no
irreducibility, admissibility, cuspidality, finite-length or positive-rank
hypothesis and proves neither an irreducible quotient nor finite length. The
actual positive-half covariance and right-translation induction are reused
without changing their carrier or normalization.
