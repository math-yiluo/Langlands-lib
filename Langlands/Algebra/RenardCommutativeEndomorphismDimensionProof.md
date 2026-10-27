# Proof of Renard C.I for commuting endomorphisms

`Langlands.Renard.commutativeEndomorphismDimension.{uV}` proves the published
proposition `Langlands.Renard.CommutativeEndomorphismDimensionStatement.{uV}`
from `Langlands.Algebra.RenardCommutativeEndomorphismDimensionStatement`. The
type of the theorem is exactly that proposition, with the same arbitrary
carrier universe `uV`. No hypothesis is added, and the statement module is
imported unchanged.

## Statement proved

For every finite-dimensional complex vector space `V : Type uV`, every
natural number `l`, and every family `a : Fin l → Module.End ℂ V` with
`∀ i j, Commute (a i) (a j)`, put
`R = Algebra.adjoin ℂ (Set.range a)` and `k = Module.finrank ℂ V`. Then

```text
(Module.finrank ℂ R : ℝ) ≤
  Real.rpow (k : ℝ) (2 - Real.rpow 2 (1 - (l : ℝ))).
```

Both powers are real powers and both subtractions are real. This is the
lemma of David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, Appendix C.I, printed p.275 / one-based
PDF281: `dim R ≤ f_l(k) = k^(2 - 2^(1-l))`. Its proof ends on printed
p.276 / PDF282. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The statement Markdown records the source comparison and the 2010 errata.

## Exponent comparison

`Langlands.Renard.renardExponent_eq_dimensionExponent` proves, for every
`l : ℕ`,

```text
2 - Real.rpow 2 (1 - (l : ℝ)) = Langlands.CommutingDimension.dimensionExponent l.
```

The right side is defined in `Langlands.Algebra.CommutingDimensionNumerics`
as `2 - 2 / (2 : ℝ) ^ l`, with a natural-number power of the real number
`2`. The proof unfolds this definition, rewrites `Real.rpow` as the real
power `^`, and applies Mathlib's `Real.rpow_sub` with base `2 > 0`:
`2^(1 - l) = 2^1 / 2^(l : ℝ)`. Then `Real.rpow_one` gives `2^1 = 2`,
and `Real.rpow_natCast` turns the real power `2^(l : ℝ)` into the natural
power `2^l`. These rewrites hold for every `l`, including `l = 0`. In that case
both exponents are `0`: `2 - 2^1 = 0` and `2 - 2 / 2^0 = 0`.

## Implemented proof

The theorem introduces `V`, its additive group, complex module and
finite-dimensionality instances, `l`, `a` and the commutation hypothesis.
It rewrites the exponent of the goal with the comparison above and rewrites
the outer `Real.rpow` as `^`. The goal is then literally the conclusion of
the existing Library theorem
`Langlands.CommutingDimension.commuting_dimension` from
`Langlands.Algebra.CommutingDimensionPrimary`:

```text
(Module.finrank K (Algebra.adjoin K (Set.range a)) : ℝ) ≤
  (Module.finrank K V : ℝ) ^ dimensionExponent l,
```

specialized to the field `K = ℂ` and this `V`. That theorem holds for any
algebraically closed field and any finite-dimensional vector space in an
arbitrary universe. Its hypotheses are the same pairwise commutation of
the same family. Its only extra instance, `IsAlgClosed ℂ`, is supplied by
Mathlib's `Complex.isAlgClosed` from `Mathlib.Analysis.Complex.Polynomial.Basic`,
which this module imports. The specialization therefore adds no hypothesis.
The natural-power theorem `commuting_dimension_nat` and the separate
natural-power target `Langlands.CommutingEndomorphismDimensionStatement`
are not used.

## Corner cases

The reused theorem has no positivity, nontriviality, nilpotence,
diagonalizability, basis or distinctness assumption. It therefore covers
every case of the target:

- For `l = 0`, `commuting_dimension` uses its zero-generator case: the
  generated algebra is the scalar algebra, of dimension at most one, and the
  exponent is `0`, so the bound is `≤ 1`. The comparison lemma shows that
  Renard's exponent is also `0` there.
- For the zero vector space, `k = 0`. When `l > 0` the exponent is positive
  and the bound is `0 ≤ 0`, because the endomorphism algebra is zero. When
  `l = 0` the bound is `0 ≤ 0^0 = 1`. Both are instances of the reused theorem.
- Repeated or non-distinct generators, and generators that are scalars, are
  allowed, because the family is arbitrary.

## Proof route compared with the source

The Library theorem follows Bernstein–Zelevinsky (1976), Lemma 4.10 and
§4.12, rather than Renard's text. It is an alternative route to the same bound,
and is permitted by the task. Renard decomposes `V` successively into
characteristic subspaces of `a_1, …, a_l` and uses convexity of `f_l`. He then
replaces the generators by their nilpotent parts and introduces the maximal
dimension `φ_l(k)` for nilpotent generators. Next he proves the recurrence
`φ_l(k) ≤ φ_l(⌊k - φ_l(k)/k⌋) + φ_{l-1}(k)` from the filtration `I^i V`, a
complement `W` of `I V` and the splitting `R = R' + R''`. He concludes by a
contradiction argument on PDF282.

The reused Library proof instead uses Mathlib's simultaneous generalized
eigenspaces. These form an independent family spanning `V` that every
element of the commutative algebra preserves. Restriction embeds the algebra
into the product of its restrictions. A real power with exponent at least
one is superadditive. After subtracting the eigenvalues, the restricted
generators are nilpotent, and
`Langlands.CommutingDimension.nilpotent_dimension` bounds each restriction.
That nilpotent bound is proved by induction on `l` and strong induction on
the dimension. It uses the invariant subspace spanned by the image of the
generators, the estimate `dim C ≤ s·m`, and the splitting
`dim C ≤ dim B + dim(C|W)`. It closes the induction with the direct real
inequality `real_dimension_step` instead of Renard's contradiction with
`φ_l`.

This module formalizes only the final bound. It does not formalize Renard's
particular intermediate assertions: the maximal-dimension function `φ_l`,
the floor recurrence, monotonicity of `φ_l`, or the contradiction step. Those
remain with the parent Renard program.

## Credit

Worker 307 wrote the general-field proof that this module imports:
`commuting_dimension`, `dimensionExponent`, the nilpotent estimate and the
primary-decomposition helpers in the `CommutingDimension*` modules. Worker
746 wrote the exponent comparison and this specialization to Renard's
real-power target.

## Verification

The theorem is checked by the project's Lean service, which reports its kind,
universe parameters and axioms. It uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`, with no `sorry`, `admit` or new axiom. It
is submitted as a `lean.proof` whose statement declaration is
`Langlands.Renard.CommutativeEndomorphismDimensionStatement`. Machine
validation runs a Lake build and an exact-target check, and independent
semantic review compares this Markdown with the Lean.
