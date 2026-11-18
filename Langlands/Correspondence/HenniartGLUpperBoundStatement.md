# The GL-side upper bound for refined supercuspidal orbit strata

`Langlands.Henniart.SupercuspidalStratumUpperBoundStatement.{uK, uV}` states
that for every prime `p`, every p-adic field `K : PadicField.{uK} p`, and every
`k s f : ℕ`, the extended cardinality of `S_K(n, s, f)` is at most
`ν(n, f, s; q_K)`, where `n = k + 1` and `q_K` is the size of the residue field
of `K`. The field universe `uK` and the representation carrier universe `uV`
are independent.

`S_K(n, s, f)` is `Numerical.supercuspidalRefinedStratum K k s f`,
the set of unramified-twist orbits of supercuspidal classes of `GL_n(K)` with
Swan exponent `s` and torsion number `f`. The Swan exponent uses the finite
conductor exponent minus `n` with truncated subtraction. The torsion number
counts the unramified twists that fix the class. The right-hand side is the
natural number `Numerical.polarPartCount q_K n f s`
coerced to `ℕ∞`, with `q_K` given by
`K.canonicalTopologicalData.residueCardinality`. The bound implies finiteness
of the stratum. When `f ∤ n` or `f ∤ s`, the polar-part count is zero, so the
bound asserts that the stratum is empty. See [refined strata](HenniartRefinedStrata.md)
and the [polar-part model](HenniartPolarPart.md).

## Provenance

The upper-bound formulation originates as input (I1) of Option II in the
operator's *The numerical local Langlands correspondence for GL_n: counts on
the two sides and the recommended route of proof*
(`operator-numerical-llc-route-2026-11-16`). It is the note's own formulation
of the simple-type ingredients below, given in §4.3, Remark `rem:upper`, and
used in §6, Theorem `thm:descent`. The exact GL-side count is the right-hand
equality of the note's Theorem `thm:target`.

- Theorem `thm:BK` uses Bushnell–Kutzko (1993), (6.2.1), (6.2.3),
  (6.2.5) and (8.4.1) for maximality, unramified-twist orbits,
  stabilizer sizes and exhaustion by simple types.
- Proposition `prop:T2` relates the Swan exponent to the level of the
  type, with the conductor input from Bushnell (1987), Theorem 3, and
  the level formula in Bushnell–Kutzko (1994), (3.10)(i).
- Theorem `thm:BK94` uses Bushnell–Kutzko (1994), (3.7) and (3.8) to
  count conjugacy classes of simple types by labels. The note's Lemma
  `lem:BKlabels` identifies the maximal simple-type labels with the
  polar-part model.

In the note's base case (`prop:basecase`), the Weil-side count and a numerical
injection give `ν = |W_K(n, s, f)| ≤ |S_K(n, s, f)|`, so (I1) suffices to
establish equality there. This module records the proposition for (I1).
