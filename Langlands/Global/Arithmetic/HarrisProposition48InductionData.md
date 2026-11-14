# Concrete data for the Proposition 4.8 induction

This is a derived definition interface for Harris (1998), Proposition 4.8,
printed pp.201–203, especially the induction and conditions (i)–(iii) on
p.202. It introduces no theorem or proof premise.

`Proposition48Problem` packages the data of the unchanged published
`Langlands.Global.Harris.Proposition48Statement`, with the three number
fields in `Type 0`. The local field remains in arbitrary universe `uF`.
The scalar-tower instance is included as data because the existing
`IsProposition48Datum` already requires it. Thus, from any instance of the
published hypotheses, its scalar-tower conjunct supplies this instance;
no extra mathematical hypothesis is intended.

`Proposition48Problem.IsValid` is exactly normalized reciprocity together
with the existing Section 4 datum. `HasSolution.{uF,uV}` is exactly the
existing existential conclusion, with the independently arbitrary local
factor-carrier universe `uV`: weak induction of the same character,
regular algebraicity, conjugate self-duality and a supercuspidal component
at the same auxiliary place. These definitions do not assume any global
existence theorem, local compatibility theorem or multiplicity one.

For an intermediate field `D` of the common closure `L/E` and an actual
`E`-automorphism `a` of `L`, the remaining definitions give:

- `conjugateEmbedding`: the given map `E' → L` followed by `a`;
- `conjugateField`: its field range, the actual subfield `a(E')`;
- `mackeyField`: the lattice supremum `D ⊔ a(E')`, the compositum in `L`;
- `mackeyRank`: its degree over `D`, using the inclusion algebra;
- `conjugateCharacter`: transport of `ξ` by the inverse idele-class
  isomorphism induced by `E' ≃ a(E')`;
- `mackeyCharacter`: that transported character pulled back by the genuine
  idele-class norm from `D·a(E')` to `a(E')`;
- `MackeyIndex`: the actual finite-group double-coset quotient
  `Gal(L/D) \ Gal(L/E) / Gal(L/E')`;
- `IsPrimeCyclicStep`: `D/E` is Galois, its automorphism group is cyclic,
  and its degree is prime.

Harris writes the double-coset quotient in the reverse order. Inversion
interchanges the two quotients; the convention here indexes the conjugate
field `a(E')` rather than `a⁻¹(E')`. No representative independence,
Mackey decomposition, cardinality dichotomy or inheritance of conditions
(i)–(iii) is proved by these definitions.

The normal-closure degree `inductionDegree = [L:E]` is distinct from
`mackeyRank = [a(E')D:D]`. The latter is the rank intended in the induction,
including rank one over `D=L`. This definition avoids propagating the
inconsistent rank expression in the printed argument.

The Mackey character is deliberately unmodified. Its inherited parity
may differ from `mackeyRank − 1`; no regular-algebraic or conjugate-dual
automorphic existence for it is asserted here. The change of normalization
and the half-integral twists discussed on p.191 remain separate proof
obligations. In particular, this file does not assert that the original
character is algebraic after the twist for every intermediate rank.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210,
`harris-1998-local-langlands`: Proposition 4.8 and proof, pp.201–203
(TeX `math_9611226v1.tex`, lines 1554–1675); the normalization remark,
p.191 (lines 866–875). The packaging, choice of double-coset orientation
and names are internal formalization choices derived from that proof.
