# Complex equal-rank equation for intertwiner images

`ComplexLocalEqualIntertwinerReductionStatement` is an internal reduction of
`ComplexLocalEqualFunctionalEquationStatement`, the Library formulation of the equal-rank case
of Jacquet 2009, Theorem 2.1 (i)–(iii). Its premise,
`ComplexLocalEqualIntertwinerPairStatement`, assumes absolute convergence in a right half-plane,
meromorphic continuations agreeing there, and the codiscrete functional equation for pairs
`B f` and `B' f'` from individual Whittaker intertwiners. The integrands, measures, factors and
sign are those of the Library statement. The premise remains open.

The proof first checks closure under zero and addition of pairs of kernels with fixed functional
equation factors. For a sum, it takes the larger of the two convergence thresholds and adds
the continuations. Integrability, equality with the integrals, meromorphy and the codiscrete
equality then follow by addition. The two kernels are additive separately in each Whittaker
function, including in the dual kernel where the dual functions are evaluated by precomposition.

The Whittaker model is a supremum of submodules given by intertwiner ranges. Induction on this
supremum in each argument extends the assumed image-pair result to all model vectors.
`ComplexLocalEqualHolomorphy` gives both holomorphy clauses on the resulting common half-plane.
