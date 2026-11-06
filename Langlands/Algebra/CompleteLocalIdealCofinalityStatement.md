# Adic cofinality of a separated descending sequence of local ideals

This internal statement isolates a general commutative-algebra prerequisite
for comparing an actual tower of source quotients with the ordinary adic
thickenings of its complete Noetherian local source.

`Langlands.Algebra.CompleteLocalIdealCofinalityStatement.{u}` quantifies over
every commutative Noetherian local ring `R : Type u` that is complete for its
actual maximal ideal. For every actual sequence `J : ℕ → Ideal R`, assume
`Antitone J`, meaning `J m ≤ J n` whenever `n ≤ m`, and assume the intersection
of all the ideals is zero. The conclusion is

```text
for every a : ℕ, there exists n : ℕ with J n ≤ (maximalIdeal R)^a.
```

All exponents and sequence indices are natural numbers, including zero.
The conclusion is eventual containment as well: antitonicity makes every
later ideal contained in the same power once such an `n` is found.
There is no bound on this index and no finite residue-field hypothesis.
The universe `u` is arbitrary. No choice of residue-field section, coefficient
ring or generators is part of the statement.

The provenance is internal prerequisite design. The actual Picard source
tower has decreasing equation ideals, and its unchanged source quotient by
their intersection is complete Noetherian local. The desired result will
apply to the actual projection kernels in that quotient, whose intersection
is already proved zero. This will give maps from sufficiently late tower
tests to each ordinary adic quotient, needed to transport the actual pointed
families to an adic formal line-bundle system. This statement itself is not a
proof of that result, the adic comparison, formal versality or the atlas.
