# Comparison, transport and transitivity for actual Jordan–Hölder series

Authors: Worker 244 and Worker 34. Worker 34 specified the formulation,
in coordination with Worker 242.

This module states three closely related facts about the Library's actual
composition series, plus one conjunction that a later proof can target. It
contains four `Prop`-valued definitions and no theorem. None of the facts is
proved here. Publishing them does not establish them.

All declarations are in the namespace `Langlands` and use the published
`ObjectRepFiltration`, `ObjectRepFiltration.HasSimpleFactors`,
`ObjectRepFiltration.gradedRepresentation` and `HaveSameJordanHolderFactors`
from `Langlands.Representation.Filtration.ObjectDefinitions`, together with
Mathlib's `Representation.Equiv`. That is a `k`-linear isomorphism of
carriers that commutes with the action of every element of `G`. No existing
declaration is changed.

## The statements

Every statement quantifies over a field `k : Type uK` and a monoid
`G : Type uG`. No statement assumes smoothness, admissibility, finite
dimension, nontriviality, a group structure on `G`, or a separate
finite-length hypothesis.

### Clause 1: `JordanHolderSeriesComparisonStatement.{uK, uG, uA}`

Fix an actual representation `A : Rep.{uA} k G`, two natural numbers `n` and
`m`, and two filtrations `s : ObjectRepFiltration A n` and
`t : ObjectRepFiltration A m`. If both `s.HasSimpleFactors` and
`t.HasSimpleFactors` hold, then the statement gives a bijection
`e : Fin n ≃ Fin m`. For every `i : Fin n`, the graded quotient
`(s.gradedRepresentation i).ρ` then admits a `Representation.Equiv` to
`(t.gradedRepresentation (e i)).ρ`.

This is the full Jordan–Hölder comparison for two supplied series. The
bijection matches every factor occurrence of `s` with exactly one occurrence
of `t`, so it preserves the following:

- the lengths, because `Fin n ≃ Fin m` forces `n = m`;
- the set of isomorphism classes of factors;
- the number of factors in each isomorphism class.

The statement is stronger than any one of these consequences. It is also
stronger than the published single-count proposition
`JordanHolderMultiplicityIndependenceStatement` in
`Langlands.Representation.Filtration.MultiplicityStatement`. That module is
unchanged. Deriving its counts from this clause is left to a later proof.

### Clause 2: `JordanHolderSeriesTransportStatement.{uK, uG, uA, uB}`

Fix `A : Rep.{uA} k G` and `B : Rep.{uB} k G`, an actual equivalence
`A.ρ.Equiv B.ρ`, a natural `n` and a filtration `s : ObjectRepFiltration A n`
with `s.HasSimpleFactors`. The statement says that some
`t : ObjectRepFiltration B n` exists with the following properties:

- it has the same length `n`;
- `t.HasSimpleFactors` holds;
- for every `i : Fin n`, `(s.gradedRepresentation i).ρ` admits a
  `Representation.Equiv` to `(t.gradedRepresentation i).ρ`, at the same
  index.

The intended `t` is the image of `s` under the equivalence. A later proof must
construct it. The clause only transports a supplied series. It never asserts
that an arbitrary representation has a composition series.

### Clause 3: `HaveSameJordanHolderFactorsTransStatement.{uK, uG, uA, uB, uC}`

For `A : Rep.{uA} k G`, `B : Rep.{uB} k G` and `C : Rep.{uC} k G`, the
hypotheses `HaveSameJordanHolderFactors A B` and
`HaveSameJordanHolderFactors B C` imply `HaveSameJordanHolderFactors A C`.

### Aggregate: `JordanHolderSeriesStatement.{uK, uG, uA, uB, uC}`

This is the conjunction of
`JordanHolderSeriesComparisonStatement.{uK, uG, uA}`,
`JordanHolderSeriesTransportStatement.{uK, uG, uA, uB}` and
`HaveSameJordanHolderFactorsTransStatement.{uK, uG, uA, uB, uC}`. Its five
universe parameters are independent: the coefficient field, the monoid, and
the three representation carriers.

## Reading the definitions

**Actual quotient representations.** `s.gradedRepresentation i` is a
representation of `G`. It is the quotient of step `i + 1` of `s` by step `i`,
an actual invariant subspace of `A` divided by another. These quotients are
not labels or isomorphism classes. Each comparison is a separate
`Nonempty (… .Equiv …)` between two such representations, and the carriers
may lie in different universes.

**Index bijection and multiplicities.** In clause 1, the matching is a
bijection of index sets, not a relation between sets of factors. Two factors
of `s` that are isomorphic to each other must go to two different indices of
`t`. Multiplicities are therefore retained. In BZ77's language, the multiset
`JH^0` is the same for both series. `HaveSameJordanHolderFactors` is
multiplicity-sensitive for the same reason: it uses a permutation of
`Fin n`.

**Supplied series versus assumed existence.** Clauses 1 and 2 take the series
as explicit inputs, together with proofs that their factors are simple. The
series themselves carry the finiteness these clauses need. If `A` has no
composition series, clauses 1 and 2 are vacuous for `A`. They do not assume or
assert that a composition series exists. In contrast, `HasCompositionSeriesLength`
and `HaveSameJordanHolderFactors` only assert that some series exists. Clause
3 starts from such existential witnesses. It concludes with an existential
witness and does not need to choose a canonical series.

**The middle representation in clause 3.** `HaveSameJordanHolderFactors A B`
supplies one composition series of `B`. `HaveSameJordanHolderFactors B C`
supplies another, which need not be equal to the first or even have the same
stated length. Clause 3 is therefore not just a composition of permutations.
It needs the comparison of two different series of `B`, which is clause 1 at
universe `uB`. Without that comparison, the two witnesses could not be joined.

**Degenerate cases.** Zero-length series and zero representations are
included. A filtration of length `0` has first and last steps both equal to
`0` and to all of `A`, so `A` is zero. Conversely, every graded quotient of a
series with simple factors is nonzero, so a zero representation has only
length-zero composition series. So in clause 1 with `n = 0`, also `m = 0`,
and the empty bijection meets the conclusion. These are remarks on the
statements, not proved lemmas.

## Original sources and derived content

Provenance: derived (internal algebraic formulation).

Source: I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
reductive p-adic groups. I*, Ann. Sci. ENS (4) 10 (1977), 441–472. Source ID
`bernstein-zelevinsky-1977-induced-i`; original PDF SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. Worker 244
read the following pages directly from the registered file on 2026-10-22.

- §1.2, printed p.443, PDF page 4. For an algebraic (smooth) representation
  `π` of an l-group on a complex vector space, `JH(π)` is the set of
  equivalence classes of irreducible subquotients. If `l(π) < ∞`, then
  `JH^0(π)` is "the set of irreducible quotients of Jordan–Hölder series of
  `π`", and "each element `ω ∈ JH(π)` is contained in `JH^0(π)` with some
  multiplicity". The notation treats this multiset as independent of the
  chosen series; §1.2 uses that independence without stating it separately.
  Clause 1 makes it explicit, as a bijection of factors.
- §2.16(2) and §2.17, printed p.450, PDF page 11 (with Theorem 2.9(iii),
  printed p.448, PDF page 9, for the condition `JH^0(π) = JH^0(π')`). §2.16(2)
  defines elementary maps `w : M → N` and shows that condition (iii) of
  Theorem 2.9 holds for `ρ' = w(ρ)` when `w` is elementary. Lemma 2.17 writes
  any `w` with `N = w(M)` as a composition `w_k ∘ … ∘ w_1` of elementary maps.
  "Thus the implication (i) ⇒ (iii) follows". For `GL(n, F)`, an elementary
  map transposes two neighbouring blocks. This reduction does two things
  without comment. It chains the equalities `JH^0(π_{j-1}) = JH^0(π_j)` along
  the steps, which is clause 3. It also cites Proposition 2.3(c) and (a)
  (printed p.446, PDF page 7): induction in stages and exactness. BZ77 writes
  induction in stages as an equality of functors. For actual representations
  it is an isomorphism, and moving a composition series across that
  isomorphism is clause 2. The
  use of exactness, where a filtration of an induced representation is
  refined, is a separate graded-refinement statement and is not part of this
  module.

These sources concern smooth complex representations of p-adic (more
generally l-) groups. Every statement in this module is more general: it
covers any field `k`, any monoid `G`, arbitrary carriers, and no
smoothness or admissibility. This generality is derived algebraic content,
not a claim found in BZ77. All three clauses are consequences of the
Jordan–Hölder theorem for modules over the monoid algebra `k[G]`, applied to
the Library's actual quotient representations. The BZ77 settings are special
cases. The block and induction arguments of §§2.16–2.17 are not part of this
module.

## Expected proof route (not implemented here)

The following route is a plan for a separate proof task. It is not evidence.

- Clause 1. Under Mathlib's
  `Subrepresentation.subrepresentationSubmoduleOrderIso`, a filtration with
  simple factors becomes a chain of covering steps in the submodule lattice
  of `A.ρ.asModule`. The covering-step bridge is
  `Langlands.LengthCriterionProof.hasSimpleFactors_iff_covBy` in the published
  `Langlands.Representation.Filtration.LengthCriterionProof`. With the chain
  as a `CompositionSeries`, `CompositionSeries.jordan_holder` gives a
  bijection of indices with equivalent intervals.
  `JordanHolderLattice.Iso.linearEquiv` turns each pair of equivalent intervals
  into a linear isomorphism of module quotients. The remaining step is to
  check that this isomorphism is an equivalence between the actual graded
  representations at the right indices.
- Clause 2. Take the images of the steps of `s` under the equivalence. On each
  graded quotient, the equivalence restricts and descends to an equivalence.
- Clause 3. Let the witnesses be `(s_A, s_B, e)` for `A, B` and
  `(t_B, t_C, f)` for `B, C`. Clause 1 applied to `s_B` and `t_B` gives
  `g : Fin n ≃ Fin m`, which forces `n = m`. Then `s_A` and `t_C` match through
  `e.trans (g.trans f)`, by composing three representation equivalences for
  each index.

Worker 242's unfinished draft for these proofs, cited in the task context, is
not used by this statement module.
