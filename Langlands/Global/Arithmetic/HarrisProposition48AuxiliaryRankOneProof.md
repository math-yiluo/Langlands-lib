# The auxiliary rank-one case of Harris's Proposition 4.8

`proposition48AuxiliaryRankOne` proves `Proposition48AuxiliaryRankOneStatement`
for independent universe levels `uF` and `uV`. It applies
`proposition48ExactStabilizerAuxiliaryRankOne` to the same problem, auxiliary
validity and degree-one equality. The resulting witness has rank index `r`,
cuspidal class `c`, the proof of `Q.IsSolution c`, and the complex-place
parameter comparison. The theorem returns `r` and `c` with the four solution
properties in `Q.IsSolution c`.

The imported construction uses rank index zero. It restricts the given
`ξ` to the base via the idele-class inclusion and twists the constant
cuspidal line by this character composed with the determinant. The twisted
tensor and spectral presentation gives the weak Euler comparison with `ξ`
in degree one. The parity-zero infinity type gives integral weights on the line.
Conjugate inversion gives a pairing with the conjugate contragredient, and
the local component at `Q.Ps.v` is supercuspidal by the rank-one criterion.
The projection retains the same cuspidal class with all four properties.
[Proof with complex-place parameters](HarrisProposition48ExactStabilizerAuxiliaryRankOneProof.md)

This bundled auxiliary statement is an internal formulation of the rank-one
start in Michael Harris, *The local Langlands conjecture for GL(n) over a
p-adic field, n < p*, Invent. Math. 134 (1998), 177–210. The proof of
Proposition 4.8 starts at `E₀ = L`, where every constituent has rank one.
The exact location is printed p. 202, `math_9611226v1.tex` lines 1588–1590 in
registered source `harris-1998-local-langlands`.
