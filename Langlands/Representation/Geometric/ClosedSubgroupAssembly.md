# Conditional assembly of the actual Mackey graded isomorphism

`supportGradedOrbitIsoOfExtension` constructs a natural isomorphism from the
specified `s.supportFiltration.graded i` to the actual compact orbit-piece
functor. It takes two geometric inputs: the assertion
`ClosedOrbitSectionExtension`, and an actual homeomorphism from the orbit
stabilizer's quotient onto the specified orbit with representative formula
`[q] -> [w^-1 q]`. These inputs remain to be proved separately; this
construction is not a proof of `ClosedSubgroupMackeyFiltration`.

The implemented route uses the canonical compact restriction natural
transformation. Apply section extension to the upper initial orbit union:
the ordering makes it open, contains the selected orbit, and makes that orbit
relatively closed. The resulting ambient function lies in the actual upper
support step and has the required pointwise restriction. This proves
surjectivity of each component, without choosing extensions naturally.

The previously established kernel is precisely the existing `lowerInUpper`
denominator. The natural first-isomorphism constructor therefore identifies
the existing quotient functor with the orbit piece. Its projection law says
that the class of an upper-step function is sent to its actual restriction.
Naturality follows from canonical restriction and descent; it imposes no
naturality requirement on the extension witnesses.

The construction retains all hypotheses of the published Mackey target, all
smooth complex inducing representations, and independent group and carrier
universes. It changes neither the filtration nor the ordering and has no
admissibility, finite-dimensionality, or finite-length restriction. Its
provenance is internal composition of the actual restriction, extension
interface, and quotient universal property. The geometric extension and
homeomorphism obligations are explicit inputs rather than claimed results.

Author: Worker 112.
