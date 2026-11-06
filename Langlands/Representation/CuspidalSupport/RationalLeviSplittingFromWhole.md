# Literal Levi splittings from the closed whole-category statement

This internal adapter is authored by Worker 1570. It applies the existing
closed whole-category cuspidal decomposition statement to the actual standard
Levi scheme and transports the resulting coproduct to the literal subgroup
of ambient rational points. It retains two explicit inputs: the whole-category
statement and a relative root system for the intrinsic maximal split torus
in this Levi. Neither input is proved by this file.

The Prop-valued definition
`RationalLeviCuspidalSplittingFromWholeStatement` records this conditional
implication. The theorem
`hasLeviCuspidalRemainderSplitting_of_wholeStatement`
proves that definition. It
uses the standard cocharacter and standard Levi intersection statements,
ambient connected reductivity, a maximal split torus, a generic cocharacter,
closed ambient standard unipotent subgroups and the closed selected Levi.
It derives connected reductivity of the represented Levi from the published
unrestricted dynamic centralizer theorem. The Levi's canonical point topology
is locally compact, nonarchimedean and Hausdorff by the published local-field
rational-point results. Maximal splitness is inherited by the actual torus
factor, and genericity follows from the published actual standard-family
comparison. Its unipotent subgroups are closed in the canonical topology.

The supplied intrinsic root system fixes the finite root index used in the
whole-category statement. That statement then gives an actual Boolean
coproduct whose true component has all cuspidal subquotients and whose false
component has no nonzero cuspidal subquotient. The existing transport theorem
uses the canonical multiplicative point homeomorphism and the exact proper
standard Jacquet tests to obtain the required literal-Levi splitting.

The field universe `u` and the representation carrier universe `v` remain
independent. No representation finiteness hypothesis is used. This local
adapter does not prove the unconditional rational finite embedding target.
