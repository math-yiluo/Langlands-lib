# Rank-one starting case of Proposition 4.8

`Langlands.Global.Harris.Proposition48RankOneStatement.{uF,uV}` states the
degree-one case of the existing proposition over small number fields.
For every valid bundled problem `Q` with `[Q.E' : Q.E] = 1`, it asserts
`Q.HasSolution`: a cuspidal class weakly induced from the same character,
regular algebraic, conjugate self-dual, and supercuspidal at `Q.Ps.v`.
No proof is supplied.

Harris (1998), proof of Proposition 4.8, printed p.202, starts with
`E₀ = L`. Every Mackey constituent there has rank
`[a(E')E₀:E₀] = 1` and is a Hecke character. The statement here isolates
the corresponding automorphic realization step, to be applied to
normalized degree-one child problems. It does not assert that an
unmodified Mackey character has the rank-one algebraic parity: that is
a separate normalization obligation.

The intended proof realizes the actual Hecke character on `GL(1)`.
Degree one identifies the two number fields; the existing datum supplies
the integral infinity type at this rank and conjugate inversion. The
`GL(1)` cuspidality and local supercuspidality statements must use the
Library's actual automorphic and local-factor presentations. The statement
does not assume their existence as extra hypotheses.

The local field universe `uF` and local factor-carrier universe `uV` remain
arbitrary. The statement imports the unchanged Proposition 4.8 pair
through the definition interface.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210,
`harris-1998-local-langlands`, Proposition 4.8 proof, p.202
(`math_9611226v1.tex`, lines 1591–1596). The formulation over bundled
degree-one problems is a derived interface for that base step.
