# Scalar determinant of a Weil–Deligne pair

Worker 17 authored this construction. `determinant A` is the
actual pair on the scalar line whose Weil action is the determinant
character of the original action and whose monodromy is zero.
`zeroMonodromy` supplies nilpotence and covariance.

The zero monodromy is consistent with the trace formula: `trace_monodromy`
uses Mathlib's theorem that the trace of a nilpotent linear map is
nilpotent, and that a field has no nonzero nilpotents.
`determinant_monodromy_eq_trace` proves that the chosen scalar monodromy
is multiplication by this trace. This works over every field, without
a characteristic-zero assumption.

`rank_determinant` gives rank one, even for a rank-zero input.
`determinantEquiv` uses the actual equivalence of scalar determinant
representations and verifies the zero-monodromy square. It certifies
`determinantClass` on the genuine pair quotient. A construction of the
exterior-power line and its canonical comparison with this scalar model
is not asserted.

Source correspondence: Henniart 2000, §1.2(1), printed page 440, supplies
the determinant-character convention. Tate, *Number theoretic background*,
Corvallis Part II, printed page 20, §§4.1.1–4.1.2, supplies the pair
formalism. The scalar determinant pair, its trace certificate and
quotient obligations are derived algebraic constructions. Source IDs:
`henniart-2000-simple-proof`, PDF SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`;
`tate-1979-number-theoretic-background`, PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

Dependencies are `Langlands.WeilDeligne.Basic`,
`Langlands.Weil.Representation.Determinant`, and pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`,
particularly `LinearMap.isNilpotent_trace_of_isNilpotent`. No
classification, semisimplification or continuity theorem is assumed.

## Included dual and twist modules

This contribution also includes `Langlands.WeilDeligne.Dual` and
`Langlands.WeilDeligne.Twist`, each with paired Markdown. They construct
the actual negative-transpose dual and scalar character twist, with
nilpotence/covariance proofs, maps and category laws, equivalences and
genuine quotient descent. All three modules use the same actual pair
interface; their imported representation operations retain their own
authorship and source correspondence.
