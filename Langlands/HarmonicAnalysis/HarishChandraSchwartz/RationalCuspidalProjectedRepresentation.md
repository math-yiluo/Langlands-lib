# The actual projected cuspidal right-translation representation

This derived unit specializes the right-translation construction used in
Waldspurger (2003), Theorem VIII.4.2, printed pp.330–331 (PDF pp.96–97),
to the Library's actual rational points, cuspidal kernel and central image.

`rationalCuspidalProjectedLeftSubrepresentation` is the literal right
translation action on `rationalCuspidalCentralLeftLevelSpan`. Its preimages
are the actual Schwartz functions in `rationalCuspidalLeftLevel`, whose
cuspidal condition includes convergence and vanishing of all translated
proper standard radical integrals. That condition is translation stable
by reassociating the two exterior group elements; the published rational
translation weights preserve the actual Schwartz space.

The central subgroup is the point image of the displayed split component,
and the projection uses the displayed measure and character. Under the
separately stated closed central-convergence proposition, every vector
is a raw image at the prescribed left level, and the representation is
smooth. Under that convergence proposition and the separately stated
VIII.4.1 finite-image proposition, it is admissible for every compact
open left level. The proof applies the generic compact-intersection
fixed-vector injection to VIII.4.1's actual finite projected level spans.

All field and group hypotheses and all structural choices are retained,
including arbitrary characteristic and the literal split-component
point image with arbitrary Haar measure. These are auxiliary deductions
from two separately owned propositions, not proofs of those propositions
or of either closed VIII.4.2 target. The quotient-L² form and
square-integrability arguments are not included.
