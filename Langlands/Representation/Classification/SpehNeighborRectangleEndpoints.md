# Endpoints of transposed neighboring rectangles

These internal calculations give the actual beginning and ending multisets of
`tadicMultisegment ρ l (k+1) + tadicMultisegment ρ l (k-1)`, for `k ≥ 2`.
For `x = (k-l-1)/2`, the endings are the union with multiplicity of
`x+{1,…,l}` and `x+{0,…,l-1}`. For `y = (-k-l+1)/2`, the beginnings are the
union of `y+{0,…,l-1}` and `y+{1,…,l}`. They realize the endpoint formulas in
Badulescu (2014), proof of Theorem 1(b)(ii), with arbitrary actual cuspidal datum
and independent field and carrier universes.

The proof expands the existing rectangle map and the endpoints of each centered
segment. It uses real arithmetic and retains the two occurrences of every
interior endpoint. Injectivity of real twisting on cuspidal data shows that the
greatest ending occurs at most once. Every ending is at most `x+l`, and every
beginning has index between zero and `l`. For positive `l`, the original segment
ending at `x+l` begins at `y+l-1`.

For an arbitrary rank-lower multisegment, the imported containment and endpoint
lemmas force its segment ending at `x+l` to begin strictly before index `l`.
Any chain starting there with strictly decreasing beginnings consequently has
at most `l` terms, by the imported finite-index counting lemma. This is the
first-chain bound in Badulescu's argument. A chain is expressed as actual
segments with positive real twists between their beginnings; no unconstructed
algorithm is assumed.

The greatest ending also remains present after rank lowering. If the first
selected chain has consecutive endings descending from this point, its bound
`r ≤ l` implies that every selected ending has positive index. The chain is
recorded by its actual segment occurrences `List.ofFn δ`, and a decomposition
of the multisegment into that list and its unselected remainder. Shortening
precisely that list with `Multisegment.dropLast` leaves every ending in
`x+{0,…,l-1}`. The imported selected-truncation lemma proves this by removing the
unique greatest ending and shifting only positive ending indices. This is the
remaining endpoint reduction before Badulescu's property (P) is applied.

The module does not assert that these rectangles are Aubert duals or implement
the MW recursion. Correctness, rectangle computation and property (P) remain
separate obligations.
