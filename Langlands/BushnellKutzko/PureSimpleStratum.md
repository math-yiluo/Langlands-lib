# Pure and simple strata

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Definition (1.5.5),
printed p. 43 (PDF p. 55).

`elementAlgebra β` abbreviates the actual `Algebra.adjoin K {β}` inside
`Module.End K V`. This fixes the meaning of `K[β]`; it is not a supplied
abstract extension with additional properties.

`Stratum.IsPure S` states the three defining conditions:

- `elementAlgebra S.b` is a field;
- its units, embedded into `Aut_K(V)` by the published `subfieldUnits`,
  lie in `S.chain.stabilizer`;
- `S.chain.valuation S.b = −S.n`.

An `IsField` witness gives a field structure by `IsField.toField` on the
existing generated algebra. Its action on `V` is the natural action of
a subalgebra of `End_K(V)`, and its scalar tower over `K` is inherited
from that action. No field extension or normalization theorem is assumed.

`Stratum.IsSimple S` is purity together with
`criticalExponent S.chain S.b < −S.r` in `WithBot ℤ`.
For finite critical exponent this is exactly `r < −k₀`. When
`K[b] = K`, `k₀ = −∞`, and the inequality holds for every integer `r`,
as the source's convention requires.

The ring-and-field parameters are those of `Stratum`: in particular the
same predicates apply to derived strata over an extension field using
its published integral-closure ring of integers and lattice-chain
mechanism. None of the conclusions T1–T7 is assumed as a field,
structure property or hypothesis.
