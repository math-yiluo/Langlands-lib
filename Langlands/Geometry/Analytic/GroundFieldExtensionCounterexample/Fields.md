# Trivially normed fields with two and four elements

This module supplies the two ground fields of the counterexample to base change
for weak strong atlas maps. They are `F₂`, the field with two elements, and
`F₄`, the field with four elements, each with the trivial norm. The counterexample
is spread over the modules in `GroundFieldExtensionCounterexample/`. All
declarations are in the namespace
`Langlands.Analytic.GroundFieldExtensionCounterexample`.

## Provenance

This is internal supporting material for a counterexample with K = F2 with the
trivial norm, L = F = F4, the two incomparable triple charts, and Frobenius on
one of them. The counterexample shows that a `StrongHom` need not extend along a
ground field extension. It has no source in the literature. The trivial
absolute value is Mathlib's `AbsoluteValue.trivial`. Equipping a field with an
absolute value is Mathlib's `WithAbs` construction.

## Definitions

- `trivialAbs₂` is the trivial absolute value on `ZMod 2`. It sends `0` to `0` and
  every nonzero element to `1`.
- `trivialAbs₄` is the trivial absolute value on `GaloisField 2 2`, the field
  with four elements. Decidability of equality is classical.
- `F₂ := WithAbs trivialAbs₂` and `F₄ := WithAbs trivialAbs₄` are these fields
  with the normed-field structures defined by their absolute values. They are
  `abbrev`s, so the `Field` instances, and the `Algebra F₂ F₄` instance that
  Mathlib finds, are those of the underlying fields.

## Instances and lemmas

- `Fintype F₂`, `Finite F₄` and `Fintype F₄` are transported along
  `WithAbs.equiv`. Both fields are finite, so Mathlib infers that each is a
  complete metric space.
- `norm_F₂_of_ne_zero` and `norm_F₄_of_ne_zero`: a nonzero element has norm `1`.
  `norm_F₂_le_one` and `norm_F₄_le_one`: every element has norm at most `1`.
- `IsUltrametricDist F₂` and `IsUltrametricDist F₄`: the trivial norm is
  ultrametric. Each instance is proved by cases on whether `x + y` and `x` are
  zero.
- `NormedAlgebra F₂ F₄` extends Mathlib's `Algebra F₂ F₄` instance. The bound
  `‖c • x‖ ≤ ‖c‖ ‖x‖` holds trivially for `c = 0`. For `c ≠ 0` we have
  `‖c‖ = 1`, and `‖c • x‖ = ‖algebraMap c‖ ‖x‖ ≤ ‖x‖` because every element
  of `F₄` has norm at most `1`.

So `F₂` and `F₄` are complete ultrametric normed fields, and `F₄` is a normed
`F₂`-algebra. These are the hypotheses that the Library's affinoid constructions
place on a ground field and on an extension field.
