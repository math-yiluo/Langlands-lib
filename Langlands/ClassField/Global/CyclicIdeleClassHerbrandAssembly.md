# The cyclic Herbrand quotient of actual idele classes

The theorem `cyclicIdeleClassHerbrandQuotient.{u,v}` proves the unchanged
proposition `CyclicIdeleClassHerbrandQuotient.{u,v}`. For every cyclic Galois
extension `E/F` of number fields, first and second ordinary cohomology of the
actual relative idele-class representation are finite, and

\[
 |H^2(G,C_E)|=[E:F]\,|H^1(G,C_E)|.
\]

The field universes are independent. Degree-one extensions are included.
The proof uses the actual published relative idele-class action and ordinary
`groupCohomology`, with the published lifted integer coefficients.

The actual representation maps form a short exact sequence from ordinary
units to integral ideles to their image in the idele class group. The theorem
`integralIdeleUnitSequenceExact` supplies group-level injectivity and kernel
equality; `repShortExact_of_values` promotes these to representation-level
short exactness. The integral-idele Herbrand quotient is the infinite-place
stabilizer product `D∞`: the published integral-idele assembly combines its
finite-local unit computation with the published archimedean computation.
The ordinary-unit theorem `cyclicUnitHerbrandQuotient` gives quotient
`D∞/[E:F]`, including the unit torsion and both finiteness assertions.

The generic cyclic Herbrand calculus divides these two quotients to obtain
`[E:F]` for the image of integral ideles. The number-field degree is positive,
and `HasHerbrandQuotient.pos` proves `D∞` positive, so these rational
cancellations are valid. The remaining quotient is finite by
`integralIdeleClassQuotientFinite`, hence has Herbrand quotient one. Applying
multiplicativity to `integralIdeleClassSequence_shortExact` gives the quotient
`[E:F]` for all idele classes. Finally `hasHerbrandQuotient_natCast_iff`
expresses the rational identity as the required natural-number identity
while retaining both finiteness conclusions.

The helper `cyclicIdeleClassHerbrandQuotient_of_integral_data` isolates the
four arithmetic inputs. The helper
`cyclicIdeleClassHerbrandQuotient_of_unitHerbrand` discharges the exactness,
finite quotient, and integral-idele inputs. The final theorem applies it
to the unconditional ordinary-unit theorem. The final theorem has no
additional arithmetic hypotheses.

This is the ordinary-unit specialization of the argument in Artin–Tate,
*Class Field Theory* (2009), Chapter V §3, printed p.13 (PDF page 22),
taking the distinguished set of places to contain exactly the infinite
places. The unit computation follows Milne, *Class Field Theory*, v4.03
(2020), Chapter VII Proposition 3.1, pp.207–209 (PDF pages 216–218),
through full invariant real lattices. The implemented argument reuses the
published generic cyclic calculus and arithmetic sequences. It does not
use idele-class H¹ vanishing, the second inequality, or reciprocity.

The assembly is by Worker 343. Its arithmetic inputs are imported from
separately published modules, which retain their respective authorship.
No prerequisite proof is duplicated in this module.
