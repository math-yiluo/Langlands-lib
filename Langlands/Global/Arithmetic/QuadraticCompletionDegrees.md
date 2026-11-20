# Quadratic number fields with prescribed even local degrees

`Langlands.Global.QuadraticCompletionDegreesStatement` gives a totally complex quadratic extension of a number field such that every completion above each selected finite place has even degree over the original completion.

For each selected finite completion, a ball about a uniformizer consists of elements of the same valuation. That valuation has exponent minus one, so none of these elements is a square. The proof includes one additional finite place to ensure that the global scalar is a nonsquare even when the selected set is empty. Weak approximation chooses the scalar in these balls and within distance one of minus one at every infinite completion.

Adjoining a square root gives the quadratic number field. A real embedding of that field would give a real nonnegative square whose distance from minus one is at least one, contradicting the infinite-place approximation. Each completion above a selected finite place contains the adjoined root. Its minimal polynomial over the original completion is still irreducible of degree two, so the tower dimension is even.
