# The orbit formula for wild inertia orbits: proof

`Langlands.Henniart.weilTameOrbitFormula` proves
`WeilTameOrbitFormulaStatement.{uK, uW}` (module
`Langlands.Correspondence.HenniartTameOrbitFormula`): for a p-adic field `K`,
`p ∤ m`, an open normal subgroup `J` of the Weil group contained in inertia of
index `m` in inertia, and `φ` of geometric degree one,
`C_K(p^r m, j) = (q_K - 1) · #(frobeniusStableTameOrbits K J r m j φ)` in `ℕ∞`.

The proof applies `weilTameOrbitFormula_of_parametrization` (module
`Langlands.Correspondence.HenniartTameOrbitCount`) to the theorem
`tameWeilFrobeniusParametrization` of the Frobenius parametrization of tame
fields (module `Langlands.Correspondence.HenniartTameWeilFieldsProof`). The
parametrization supplies open subgroups of inertia of every index prime to `p`
containing wild inertia, the only arithmetic input of the orbit count not
established in `HenniartTameOrbitCount` itself.

In outline (details in the Markdown of `HenniartTameTypes` and
`HenniartTameOrbitCount`): the conductor count is the number of inertia types
fixed by conjugation by `φ` with rank dividing `p^r m` and break at most
`j / (p^r m)`; each such type lies over one inertia orbit of wild classes; the
counted types correspond exactly to the orbits meeting the tame classes for
`J` that are stable under `φ`; and over each such orbit there are exactly
`q_K - 1` fixed types, by the Clifford fiber count and the rank-one count
`weilRankOneCount`. Source: H. Koch, *Bemerkungen zur numerischen lokalen
Langlands-Vermutung* (1984), registered as
`koch-1984-numerical-langlands-remarks`, §8, Lemmas 5–8 and formulas
(25)–(28) (PDF pp. 5–6).
