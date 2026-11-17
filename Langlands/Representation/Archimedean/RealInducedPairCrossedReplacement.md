# Crossed endpoint replacement of two linked real induction blocks

This internal arithmetic construction pairs the two lower endpoints and the two
upper endpoints of the original induction blocks. It is derived from the actual
endpoint definitions and the linked-gap equality in the Library. It asserts no
map, range equality, occurrence, spanning result or filtration.

Write `L=|d.weight|`, `M=|e.weight|`, `H=innerWeight d e k` and
`P=outerWeight d e k`. The crossed weights are the positive natural numbers
`A=P-M=H+L` and `B=P-L=H+M` from `RealInducedPairMiddleParity`. The centers are
the means of the two lower and the two upper endpoints, respectively. These data
are independent of all freely chosen presentation parities.

For a linked original pair the crossed support is `[x,u,y,v]`, where `u,v` are
the original lower and upper endpoints of `d` and `x,y` those of `e`. This
permutes the original support. The exact signed increase in squared weights is
`A²+B²-L²-M²=2HP`. Thus the crossed pair is an allowed heavier adjacent piece
whenever `H>0`, with no extra squared-weight bound.

When both original absolute weights are positive, the crossed pair is linked at
`min(L,M)-1`. Its outer weight remains `P` and its signed inner weight is `-H`.
The center difference is `(L+M)/2`; the minimum crossed weight is `k+1`, and
their maximum is `max(L,M)-min(L,M)+k+1`. These identities prove the assertions
using integer and natural-number arithmetic and the linked-gap definition.

Pairing the crossed endpoints a second time recovers
`characterOfParams L d.exponent` and `characterOfParams M e.exponent`, in that
order. Their weights are the positive normalizations of the original weights;
equality with arbitrary original signed character data is not asserted.
The proof first recovers each of the four endpoints from its mean and positive
difference, then averages the original lower and upper endpoints.

`RealInducedPairCrossedReplacementStatement` collects the support permutation,
exact weight increase, heavier-piece consequence for `H>0`, linked index,
outer and signed inner weights, and the two normalized recovery identities.
The theorem `realInducedPairCrossedReplacement` proves this proposition.
This prerequisite supplies no actual intertwining map and does not prove
`RealInducedInducedFiltrationStatement`.
