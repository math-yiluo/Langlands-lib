# Actual Jacquet classes of a supplied signed Aubert image

`Langlands.Aubert.QuasicuspidalJacquetClassStatement.{uF,uV} F T` is a
conditional algebraic statement about the actual unadjusted Aubert operator.
It ranges over every prime, supplied topological field datum, rank `n`
(including zero), ordered block shape `B`, and two actual finite-length smooth
complex representations `π` and `τ` of `GL_n(F)`. Their carriers have universe
`max uF uV`, with independent field and carrier universe parameters.

Suppose an integer `ε`, equal to `1` or `-1`, satisfies
`D([π]) = ε • [τ]` in the existing exact finite-length smooth Grothendieck
group. Suppose also that the actual normalized upper Jacquet module
`J_{B.reverse}(π)` is quasicuspidal as a representation of the whole reversed
product Levi and has a nontrivial carrier. Then the statement asserts both

1. `ε = (-1)^(n - B.length)`;
2. `[J_B(τ)]` equals the class of `J_{B.reverse}(π)` transported to the
   `B`-Levi by the existing `B.reversePermutation`.

The second conclusion is expressed using `normalizedJacquetK0` and
`leviTransportK0`. Their published generator formulas identify these values
with classes of the literal Jacquet and transported smooth objects. The
transport uses the continuous Levi conjugation equivalence with the orientation
fixed by `conjugatesLevi_reversePermutation`: from the reversed Levi to the
original Levi, by inverse-conjugation pullback. The project's normalized
upper-parabolic conventions use positive half-modulus covariance and right
translation for induction, and inverse half-modulus action on upper-unipotent
coinvariants for Jacquet restriction. All classes use the actual exact
finite-length Grothendieck groups.

This is a derived internal interface. Its proposed derivation combines the
published `JacquetCompatibilityStatement` with
`alternatingOperatorOnLevi_quasicuspidal`. The latter gives the Levi sign
`(-1)^(n - B.reverse.length)`, which is the sign in the conclusion because
reversal preserves length. The nonzero genuine class on the right has strictly
positive composition length, whereas the genuine Jacquet class on the left
has nonnegative composition length. Consequently their signed equality
determines the sign; cancellation gives the class equality.
This module defines the proposition and does not prove it.

No irreducibility or admissibility hypothesis is imposed. The signed-image
equality is an explicit premise: the statement supplies no existence of an
actual signed Aubert image. It also asserts no equivalence of the actual
representations, no generalized central-spectrum comparison, and no analytic
square-integrability or segment classification. Quasicuspidality is required
for the specified reversed Jacquet module, not for arbitrary Jacquet modules.
