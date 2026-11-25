# Frobenius on a complete DVR with perfect residue field

The definition `frobeniusUniformizerExpansionMap` forms a linear
combination of `1, π, …, π^(p-1)` in a copy of the ring with
scalar structure given by Frobenius. Applying the underlying map
to coefficients `cᵢ` gives the sum of `cᵢ^p * π^i`.

For a complete DVR of characteristic `p` with perfect residue
field, the proof lifts a `p`th root of the residue of an element,
subtracts its `p`th power and divides the difference by `π`.
Iteration gives the expansion modulo the `n`th power of `π`.
Taking `n = p` proves surjectivity of the expansion map modulo
the extended maximal ideal. Completeness of the finite free
source and separation of the target give surjectivity by the
adic surjectivity criterion. The resulting finite set of module
generators proves `finite_frobenius_of_isAdicComplete`.

This is a derived step in a proof of finiteness of normalization
for the complete DVR case of the reduced fibre theorem. It uses
the complete-base setting of Conrad's appendix to Prasad–Yu,
*On quasi-reductive group schemes*, author preprint, Theorem A.6
(p. 30). The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
