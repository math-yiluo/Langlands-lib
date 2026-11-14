# Principal-open descent of actual substitutable tuples

This derived unit constructs `SeriesPoint.basicEquiv`: actual substitutable
tuples over R are equivalent to actual substitutable tuples over a
principal-open cover that agree on all pairwise overlaps. Gluing is performed
coefficient by coefficient; nilpotence of the glued constant coefficients is
proved from their local nilpotence. In particular, taking no formal variables
gives descent of actual nilpotent coordinate tuples.

## Provenance and assumptions

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), paragraph immediately before section 2, permits formal groups
obtained by gluing formal groups over localizations of the base. The registered
source is `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
This unit supplies derived point-level localization infrastructure motivated
by that convention. The coefficient gluing theorem is the existing Mathlib
structure-sheaf theorem
`Localization.existsUnique_algebraMap_eq_of_span_eq_top`; no separate
point-descent assertion is attributed to Drinfeld.

R is an arbitrary commutative ring. The coordinate type σ and the formal
variable type κ are in `Type`. The construction of glued `SeriesPoint`s
requires σ finite; κ is arbitrary. For finite σ, the defining `HasSubst`
condition follows from nilpotence of each constant coefficient. The set
s ⊆ R may be infinite and is required to span the unit ideal. No common
nilpotence exponent across the localizations is assumed, and R need not be
reduced or Noetherian. This unit concerns tuples over localizations of one
ring. It does not compare varying formal chart laws or prove atlas refinement,
independence of presentations, a general site sheaf condition, moduli
representability, heights, framing or level structures. It does not yet
package compatibility with formal group addition or scalar action.

## Detection of nilpotence

`isNilpotent_of_basic_cover` proves that an element x of R is nilpotent if
its image is nilpotent in every R[1/a], for a in s. The proof uses
`nilpotent_iff_mem_prime`. Given a prime ideal J, the span hypothesis supplies
a chart element a outside J. If x maps to a nilpotent element in R[1/a],
some power of x vanishes there. The localization equality criterion then
supplies an equality a^m x^n = 0 in R. Primality and a ∉ J imply x ∈ J.
Thus x belongs to every prime ideal and is nilpotent. This argument handles
infinite covers without choosing a bound for the local exponents.

## Matching tuples and coefficient gluing

`SeriesPoint.BasicCompatible s z` requires that the tuple z(a) over R[1/a],
restricted to R[1/(ab)], equals the similarly restricted tuple z(b) for every
ordered pair a,b. The restriction maps are Mathlib's actual localization
ring homomorphisms `awayToAwayRight` and `awayToAwayLeft`.

`SeriesPoint.ext_basic` proves equality of global tuples from equality of all
local restrictions. Tuple and power-series extensionality reduce to each
coefficient, and `Localization.algebraMap_injective_of_span_eq_top` detects
its equality on the cover. This separation statement does not require
finiteness of σ.

`glueBasicCoefficient` chooses the unique coefficient supplied by the
structure-sheaf gluing theorem. The coefficient matching premise is obtained
by evaluating the tuple matching equation at one coordinate and one monomial.
`glueBasicCoefficient_spec` states its required value in every localization.

`glueBasic` assembles these coefficients into a tuple of power series. For
each coordinate, the constant coefficient restricts to the constant
coefficient of each prescribed local `SeriesPoint`, hence is locally
nilpotent. `isNilpotent_of_basic_cover` proves it globally nilpotent, and
finite σ gives the actual `HasSubst` proof. No substitutability certificate
for the glued tuple is assumed. `glueBasic_map` proves that the resulting
actual tuple restricts to the prescribed one by coefficient extensionality
and `glueBasicCoefficient_spec`.

## The constructed equivalence

`basicCompatible_map` checks that restrictions of a global tuple agree on
overlaps. After tuple and coefficient extensionality, both sides equal the
image of the original coefficient in R[1/(ab)] by the localization lift
identities. `MatchingBasic s` is the subtype of the product of local tuple
carriers satisfying these equations.

`basicEquiv s hs` sends a global tuple to its actual localized restrictions.
Its inverse is `glueBasic` applied to the supplied matching family. The left
inverse follows from `ext_basic` and the gluing restriction formula. The
right inverse follows from that same formula at each chart. This supplies
both existence and uniqueness of gluing. When κ is `Empty`, the existing
`SeriesPoint.nilpotentEquiv` identifies these carriers with tuples of
nilpotent elements, so the construction applies to the point carriers used
by the formal-module atlases.
