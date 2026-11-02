# Reversed duals of finite free cochain complexes

Author: Worker 1015.

This internal construction defines `reversedDual g C`, whose degree `i`
term is `Module.Dual R (C.X (g - i))` and whose differential is the
transpose of the reversed differential of `C`. Here `g` and all complex
degrees are arbitrary integers, and `R` is any commutative ring in an
arbitrary universe `u`. No sign is added: transposition reverses the
order of composition, and the transpose of a zero composite is zero.
The module also records the term and evaluation formulas.

The two bound lemmas send an upper term bound `b` to the lower term bound
`g - b`, and a lower term bound `a` to the upper term bound `g - a`.
They use that the dual of the zero module is zero. Consequently
`isFiniteFree_reversedDual` preserves bounded finite free complexes:
its termwise finiteness and freeness follow from Mathlib's corresponding
dual-module instances.

`reversedDualBidualIso` identifies `C` with its twice reversed dual when
every term of `C` is finite free. Its degree-`i` component first transports
along `g - (g - i) = i` and then uses `Module.evalEquiv`. The evaluation
maps commute with the double transpose of each differential because
both resulting functionals evaluate a given functional on that
differential's value. The proof checks the transports using
`HomologicalComplex.XIsoOfEq`.

This is internal supporting infrastructure, derived directly from
Mathlib's dual maps and finite-free evaluation equivalence. It adds no
external source assertion. No exactness of a dual complex, comparison
with a Koszul resolution, or homology duality assertion is made here.
