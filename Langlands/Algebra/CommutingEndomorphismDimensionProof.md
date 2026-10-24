# Proof of the commuting endomorphism dimension bound

`Langlands.commutingEndomorphismDimension.{uV}` proves the published
proposition `Langlands.CommutingEndomorphismDimensionStatement.{uV}` from
`Langlands.Algebra.CommutingEndomorphismDimensionStatement`. The type of the
theorem is exactly that proposition, with the same arbitrary carrier universe
`uV`. No hypothesis is added.

## Statement proved

For every finite-dimensional complex vector space `V`, every natural number
`l`, and every pairwise commuting family `a : Fin l → Module.End ℂ V`, put
`D = Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a))` and
`m = Module.finrank ℂ V`. Then

```text
D ^ (2 ^ l) ≤ m ^ (2 ^ (l + 1) - 2),
```

with natural-number powers and natural subtraction. This is the
natural-power form of Bernstein–Zelevinsky (1976), Lemma 4.10, printed
p.39, proved in §4.12, printed p.40 (registered source
`bernstein-zelevinsky-1976-representations-gln`). The statement Markdown
explains how this form follows from the source's real exponent
`2 - 2^(1-l)`.

## Implemented proof

The proof introduces the carrier `V`, its additive group, complex module
and finite-dimensionality instances, the number `l`, the family `a`, and
the commutation hypothesis. It then applies the existing Library theorem
`Langlands.CommutingDimension.commuting_dimension_nat` from
`Langlands.Algebra.CommutingDimensionPrimary`, specialized to the field
`ℂ` and this `V`.

That theorem holds for any algebraically closed field `K` and any
finite-dimensional `K`-vector space. Its conclusion is the same natural-power
inequality, with `K` in place of `ℂ`. The only extra assumption it uses,
`IsAlgClosed ℂ`, is a Mathlib instance from
`Mathlib.Analysis.Complex.Polynomial.Basic`, which this module imports.
Thus the specialization introduces no hypothesis. All edge cases of the
target, including `l = 0` and the zero vector space, are covered because the
general theorem has no positivity or nontriviality assumption.

The module does not reprove the bound. The general theorem rests on the
nilpotent estimate in `Langlands.Algebra.CommutingDimensionNilpotent` and on
the primary decomposition into simultaneous generalized eigenspaces in
`Langlands.Algebra.CommutingDimensionPrimary`. It then clears the real
exponent by raising both sides to the power `2^l`.

## Credit

Worker 307 wrote the general-field proof infrastructure that this theorem
imports. This includes `commuting_dimension_nat` and the `CommutingDimension*`
helper modules. Worker 277 wrote this specialization wrapper.

## Verification and publication

The theorem is checked with the project's Lean service, which reports its
kind, universe parameters and axioms. It must use only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`, so it contains no `sorry`,
`admit` or new axiom. The theorem is submitted as a `lean.proof` naming
`Langlands.CommutingEndomorphismDimensionStatement` as its statement
declaration. Machine validation runs a Lake build and an exact-target
check. It also checks that the statement pair and its imports are
unchanged. Independent semantic review compares this Markdown with the
Lean. Publication in the Library follows acceptance.
