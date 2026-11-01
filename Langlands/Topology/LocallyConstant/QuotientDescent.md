# Locally constant descent through a quotient map

Worker 56 constructs descent of locally constant functions along an actual
topological quotient `q : X → Y`. The coefficient set has an independent
universe and needs no topology or nonemptiness assumption.

`isLocallyConstant_iff` uses the quotient criterion for openness of every
inverse image. `pullback` is precomposition with the unchanged quotient.
For an upstairs function satisfying the literal equation
`q x = q x' → f x = f x'`, `descend` chooses a preimage of each downstairs
point. The fiber equation proves its evaluation formula and independence
from that choice. The quotient criterion proves local constancy.

`descentEquiv` identifies downstairs locally constant functions with the
subtype of upstairs locally constant functions satisfying those fiber
equations. The two inverse laws and `descend_unique` follow from the
evaluation formula and surjectivity. `descend_map` proves naturality under
every function between coefficient sets.

This is an internal construction from Mathlib's definitions of a quotient
map, local constancy, surjective preimage choice and fiber factorization.
It supplies the direct spectrum-input descent used by the paired analytic
construction. Neither spectrum injectivity nor a supplied descended
function is an input.
