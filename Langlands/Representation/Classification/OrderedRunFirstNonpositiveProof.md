# Proof of the first nonpositive ordered run

The theorem `Langlands.Classification.orderedRunFirstNonpositive` proves
exactly `Langlands.Classification.OrderedRunFirstNonpositive`.

If every endpoint sum were positive, each positive natural length times
that sum would be positive. Summing over the nonempty `Fin k` contradicts
the nonpositive total. The proof forms the finite set of positions with a
nonpositive sum and selects its minimum.

For an earlier position `j`, minimality gives `0 < a j + b j`.
Monotonicity gives `a j <= a i`, and the selected sum gives
`b i <= -a i <= -a j < b j`. These are the required endpoint comparisons.
When `k > 1`, `Fin k` has another index `j`. Its positive natural length,
together with nonnegativity of all the other lengths, makes the selected
length strictly smaller than the total.

The implementation uses finite-sum positivity, the minimum of a nonempty
finite set, linear arithmetic, and the strict comparison of one summand
with a sum having another positive summand. It imports no representation
theory. It proves no actual run decomposition, Jacquet transfer, contained
segment commutation, Casselman criterion, or classification result. The
statement's paired Markdown records the original motivation and the
separate application obligations.
