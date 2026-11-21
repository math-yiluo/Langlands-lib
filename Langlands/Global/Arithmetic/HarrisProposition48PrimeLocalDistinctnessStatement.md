# Actual local witnesses for the general-position prime orbit

`Proposition48PrimeLocalDistinctnessStatement` isolates the local step of
Harris (1998), Proposition 4.8, printed p. 203, from the cyclic induction
and its supercuspidality theorem. The input is the actual transported raw
basepoint over the step field `D`, with an actual supercuspidal presentation at
the unique place above the auxiliary place. Its field and character identifications
come from `IsPrimeOrbitBasepoint`. The statement supplies a family indexed by
the powers of the cyclic generator. Each member has an actual raw presentation
at that same place. Their components are supercuspidal and their local classes
are pairwise distinct. The local class at the identity power is the class of the
supplied basepoint component. The resulting global freeness is stated in the
form used by the cyclic regular induction and orbit-lift premises.

The parent general-position hypothesis implies irreducibility of the full
local Weil induction at the bottom of its witnessing tower. In the prime-orbit
case the step field lies in the inducing field and the corresponding local Weil
subgroup is normal of prime index. Mackey decomposition and irreducibility of
the full induction distinguish the conjugate Weil constituents over that subgroup.
The uniqueness of the auxiliary place lets the comparison use the displayed
completion for every power.

For rank greater than one, the common determinant correction makes the
actual comparison presentations regular algebraic. One applies
`HarrisSupercuspidalLocalComparisonStatement` to those presentations only
once their supercuspidality, conjugate self-duality and pure weak associations
with common weight and coefficients are available. Its forward implication
then distinguishes their local classes by contraposition. The determinant
twist is the same on each raw local component, so one can cancel it. This
uses the general-coefficient remark on pp. 202–203 and the half-integral
normalization on pp. 191 and 195. In rank one, weak induction identifies the
actual local character via the central action, and local class field theory
distinguishes the scalar characters. The statement keeps the local-field and
spectral carrier universes independent.
