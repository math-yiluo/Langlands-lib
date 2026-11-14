# Underlying-point supports on the analytic étale site

`EtalePointLifting L` says that an `L`-valued point lifts to any étale
object whose image contains its underlying point.

`pointFibre_nonempty_of_complement` derives such a lift from the point
axioms when the complement of that underlying point is represented by an
étale object. The two structural arrows generate a covering sieve because
their images jointly cover the underlying analytic space. Applying the
point axiom at the identity object gives a lift through one arrow. The
complement arrow cannot contain a lift of this point, so the lift factors
through the other object.

`etalePointLifting_of_openDomains` applies this argument to the actual
open analytic domain complementary to the point. It assumes
`EtaleOpenDomainStatement X` and Hausdorffness and does not assert an
unconditional proof of that geometric statement.

These are internal consequences of the published definitions of the
analytic étale site, field-valued point functor and open analytic domains.
They isolate the geometric input to support saturation in the
compact-support comparison.
