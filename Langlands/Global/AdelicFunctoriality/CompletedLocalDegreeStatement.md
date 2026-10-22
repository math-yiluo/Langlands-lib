# Completed local degree lower bound

`CompletedLocalDegreeLowerBound` is a proposition for arbitrary number fields
`K : Type u` and `L : Type v`, with their given `Algebra K L`, and arbitrary
height-one primes `p` of `𝓞 K` and `q` of `𝓞 L` such that `q` lies over `p`.
It asserts

`e(q/p) * f(q/p) ≤ [L_q : K_p]`.

The two universe parameters are independent. The left side uses Mathlib's
`Ideal.ramificationIdx` and `Ideal.inertiaDeg` for the actual integer rings
and actual prime `q`. The right side uses Mathlib's actual valued adic
completions. Its algebra structure is the scoped `FiniteExtension` instance
from the published `Extension` module: this instance is constructed from
`FiniteExtension.completionMap`, the continuous extension of the given
number-field embedding. It is not an arbitrary algebra structure or a field
equivalence supplied as data. Finite dimensionality of this completed
extension is already proved by Mathlib and used by `Extension`.

This is an internal arithmetic prerequisite extracted from the published
`CompletedTensorComparison` obligation in `NormStatement`. It is not a
claim that the local inequality has already been proved. No residue-field
comparison, classification of extensions, separability certificate,
local-degree sum, or tensor-map bijectivity is a hypothesis.

The intended reduction is as follows. Mathlib's fundamental ramification
identity sums the products `e(q/p) * f(q/p)` over all actual primes above
`p` to obtain `[L : K]`. The asserted inequalities therefore give the
lower bound on the sum of completed degrees. Surjectivity of the canonical
finite tensor map, proved in Worker 50's separate reduction draft, gives
the reverse dimension inequality; equality then gives injectivity.
That reduction and a proof of this proposition require their own proofs
and independent acceptance. This file supplies neither of them.

The statement is derived project content: it isolates just the arithmetic
inequality needed for that dimension argument, rather than transcribing
a separately cited literature theorem. The original completed tensor
decomposition is documented in the published `Norm` and `NormStatement`
modules. This prerequisite leaves the infinite-place comparison, norm
compatibility, and idele-class descent outside its scope.
