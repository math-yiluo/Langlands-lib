# Unproved combinatorial Moeglin–Waldspurger targets

Worker 963. Every declaration in this module is a proposition definition, not
a proof. The targets refer to the actual total recursion `dual` from the
paired algorithm module; none is a field or premise of that recursion.

`SupportPreservation` asserts equality of multisets of integer points, with
all multiplicities. `Involutivity` asserts `dual (dual a) = a` for every input,
including the empty input. Their original convention is
Moeglin–Waldspurger (1986), II.1–II.2, printed pp.148–149, the multisegment
involution constructed in II.2; the main comparison theorem in the introduction,
printed pp.136–138, identifies it with the representation-theoretic involution.
Badulescu (2014), `1110.5080.tex` lines 116–136, describes this same algorithm
as computing the multisegment of the Aubert dual. The targets use the
shortest-segment algorithm and the Langlands-head convention recorded there.

`EndingBound` is Badulescu's property (P), `1110.5080.tex` line 138.
For integers `b` and a natural number `k`, it assumes every input ending lies
in the half-open integer range `[b,b+k)`, which has exactly `k` integer points.
It concludes that every output interval has length at most `k`. For `k > 0`
this is exactly containment of the input endings in the closed integer segment
`[b,b+k-1]` of length `k`. Allowing `k = 0` adds the vacuous empty-input case.
The premise concerns ending membership, so multiplicities do not change it.

`ThicknessBound` is property (P'), lines 140–142: every output interval has
length at most the number of input interval occurrences, counted with
multiplicity. This pointwise form avoids a separate convention for maximum
length of the empty output and is equivalent to the source's maximum-length
form for nonempty multisegments. `CombinatorialProperties` simply groups the
four separately named targets. No proof of any of them is supplied here.
