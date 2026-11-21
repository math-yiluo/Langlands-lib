# The full-datum rank-one case of Harris's Proposition 4.8

`Langlands.Global.Harris.proposition48RankOne.{uF,uV}` proves
`Proposition48RankOneStatement` for independent local-field and carrier
universes. For a valid full datum `Q` with `[Q.E' : Q.E] = 1`, it obtains
a cuspidal class weakly induced from `Q.ξ` that is regular algebraic,
conjugate self-dual, and supercuspidal at `Q.Ps.v`.

The proof extracts normalized reciprocity, the field and normal-closure
conditions, the auxiliary place conditions, general position, and the
character conditions from full validity. These fields give
`Q.IsAuxiliaryValid` on the same problem, with the same parity
`[Q.E' : Q.E] - 1`. Applying `proposition48AuxiliaryRankOne` at the given
degree equality gives `Q.HasSolution`.

Harris's proof of Proposition 4.8 starts the Mackey induction at
`E₀ = L`, where each constituent has rank one and is a Hecke character.
The extraction of auxiliary validity is an internal consequence of the
Library's bundled full and auxiliary formulations of that step.

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), 177–210, registered source
`harris-1998-local-langlands`, proof of Proposition 4.8, printed p. 202,
`math_9611226v1.tex`, lines 1588–1590.
