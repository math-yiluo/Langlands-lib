# Finite signed chamber lattice charts

`Langlands.FiniteSignedChamberLatticeStatement.{uΔ,uX}` concerns a finitely
generated torsion-free abelian group `X`, with a finite family of integral
pairings. The label and lattice universes are independent. For every subset
of labels, a supplied standard element has zero pairing on that subset and
strictly positive pairing on its complement.

There are a natural number `k` and finitely many charts, indexed by the
functions `Fin k → Bool`. Each chart has generators indexed by
`Δ ⊕ Fin k`. Its generators are integrally linearly independent and every
pairing is nonnegative on each generator. For every integer lower bound `-B`,
a finite set of translates covers every lattice element whose pairings are
at least `-B`, using nonnegative integral combinations in one of those charts.
The generators are chosen before `B`; the translates may depend on `B`.

This internal strengthening of `FiniteChamberLatticeStatement` retains the
common pairing kernel in the charts. The separated root-axis generators of
that result are independent modulo the kernel. The kernel is a finite free
integral module. A basis of it supplies the additional `k` generators, with
one choice of signs for each chart. Every integral basis-coordinate tuple
has one such sign choice and nonnegative magnitudes. Applying the pairings
and then independence of the kernel basis proves independence of the joined
family. This also covers empty labels and a zero-dimensional kernel.

The statement chooses no algebraic torus, character, rational point,
topology, Cartan decomposition or representation. Those comparisons and
existence results remain separate obligations.
