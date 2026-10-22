# Completed local degree lower bound

`completedLocalDegreeLowerBound` proves the complete published proposition
`CompletedLocalDegreeLowerBound`. For arbitrary number fields `K : Type u` and
`L : Type v`, their given `Algebra K L`, and actual height-one primes `q` above
`p`, it proves

`q.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 K) ≤ [L_q : K_p]`.

The universe parameters `u` and `v` are independent. Here `K_p` and `L_q` are
Mathlib's actual adic completions, and their algebra is exactly the scoped
`FiniteExtension` algebra obtained by continuously extending the original
number-field embedding. The statement and all its imported files are unchanged.

The proof uses the actual adic integer rings
`R = p.adicCompletionIntegers K` and `S = q.adicCompletionIntegers L`.
The published `CompletedRamification` module supplies their canonical algebra,
its local-homomorphism property, the compatible fraction-field towers, and the
identity between the local and global ramification indices. That identity is
proved there by comparing normalized valuations on the actual completion map
and evaluating on a uniformizer. Mathlib supplies the DVR and fraction-field
instances and finite dimensionality of `L_q` over `K_p`.

The first new lemma, `FiniteExtension.adicResidueEquiv_algebraMap`, verifies that
the canonical residue comparisons from `CompletionResidueAdic` commute with
the extension algebra maps. On a representative from `𝓞 K`, both sides reduce
the same embedded integer in `S`. The proof uses quotient surjectivity, the
published reduction formula `adicResidueEquiv_mk`, and
`FiniteExtension.completionMap_coe`. Thus these residue comparisons are
compatible with the given extension scalars. The imported one-field comparison
and its density argument are reused without modification.

`FiniteExtension.completionIntegers_inertiaDeg` identifies the local and global
inertia degrees numerically. Since the completed integral map is local, its
maximal ideals lie over one another. Mathlib's
`Ideal.inertiaDeg_eq_of_isMaximal` expresses the local inertia degree as the
finrank of the canonical residue-field extension. The imported
`CompletionResidueAdic` instances prove that both residue fields are finite.
Consequently `Module.natCard_eq_pow_finrank` gives

`absNorm(q) = absNorm(p) ^ localInertiaDegree`.

The cardinalities in this formula are identified with the global ideal norms by
`CompletionResidue.card_adicResidueField`. For the original integer-ring
extension, Mathlib's `Ideal.absNorm_pow_inertiaDeg` gives the same formula with
the global inertia degree. The norm of the nonzero prime `p` is greater than
one, so injectivity of exponentiation equates the two exponents. This argument
uses the actual scalar structures for both finranks; it does not choose a new
field algebra or require transport of a basis across the residue comparisons.
The commuting-square lemma above additionally records their scalar compatibility.

Finally, the independently published general theorem
`Langlands.LocalField.dvrDegreeLowerBound` applies to `R`, `S`, `K_p`, and `L_q`.
It bounds the product of the local ramification and inertia degrees by the
completed field degree. Rewriting the two proved comparisons gives the exact
target. The general theorem does not assume that `S` is finite over `R`; its
published proof obtains the bound from quotient module lengths and finite spans
of lifts over a PID. No such finiteness hypothesis is added here.

This is an internal derived proof of the published arithmetic prerequisite,
using the named Library results and pinned Mathlib results above. It is not a
transcription of a separate literature proof. No separability certificate,
classification of local extensions, desired degree bound, completed tensor
decomposition, arbitrary field equivalence, or additional axiom is assumed.
The file proves this one local inequality and the stated supporting comparisons;
it does not prove tensor-map bijectivity, norm compatibility, or idele-class
norm descent.
