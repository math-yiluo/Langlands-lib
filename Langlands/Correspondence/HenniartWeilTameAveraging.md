# Fixed-cutoff tame averaging of Weil conductor counts

`Langlands.Henniart.TameTotallyRamifiedExtensions K m` is the type of actual
finite intermediate fields in the fixed algebraic closure of `K` satisfying
`Numerical.IsTameTotallyRamifiedOfDegree` for the literal inclusion. In
particular, distinct conjugate fields are distinct indices. Its elements
bundle the degree `m`, residue degree `1`, and `p ∤ m` conditions, with
no chosen ordering.

`Langlands.Henniart.WeilTameAveragingStatement.{uK,uW}` says that for every
p-adic field `K`, every `r`, `m`, and `j`, with `p ∤ m`, there is an enumeration
of that type by `Fin m`, and with this enumeration
\[
  \sum_{L} C_L(p^r,j) = m\,C_K(p^r m,j).
\]
Here `C` is the existing `Numerical.weilConductorCount` (in extended natural
numbers), with rank `n` encoded by `n - 1`. The ranks are positive since `p`
is prime and `p ∤ m`. Both sides use the same cutoff `j`; no formula for the
pure-rank counts or truncation at a ramification bound is assumed. The two
universe parameters are independent.

**Provenance (derived).** H. Koch, *Bemerkungen zur numerischen lokalen
Langlands-Vermutung* (1984), registered as `koch-1984-numerical-langlands-remarks`,
§8, printed p. 113 (PDF p. 6), Lemmas 5–8 and equations (25)–(28). Lemma 5
counts actual embedded fields. The pair counts in (25)–(27) compare the
count over `K` with the total over those fields, retaining the common
uniformizer-determinant normalization of §8, before (28) applies the pure-rank
input. In twist-orbit notation this is the field average above: with a
common determinant exponent times dimension, each orbit with irreducible
inertia restriction contributes the same number of representatives on
both sides. The comparison preserves the cutoff `(n / dim ρ) * Sw(ρ)`,
using tame totally ramified induction (Koch, §4, equation (7), printed p. 109).
The statement expresses this intermediate comparison in the Library's
Weil-side notation, not a same-field formula for all `r` and `m`.

`Langlands.Henniart.WeilTameReductionFromAveragingStatement.{uK,uW}` is the
implication from this average to the previously published
`WeilTameReductionStatement.{uK,uW}`. This is an internal reduction target:
for a field in the average, `e_L = m * e_K` and `q_L = q_K`, so the truncated
pure-rank hypotheses apply at `r' = r`, `d = m`, and the same `j`. Neither
proposition is proved in this module.
