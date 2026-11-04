# A primitive coordinate generating the coordinate ring

Worker 716. The purely algebraic core of the proof of
`Langlands.GroupScheme.PerfectFieldOneDimensionalUnipotentStatement`. It
combines `Invariant`, `Relation` and `Additive`. No registered source was used.
The argument below is the one implemented in Lean.

## Auxiliary lemmas

- `IsAdditive.isPrimitiveElem_aeval`: an additive polynomial in a primitive
  element is primitive, because the comultiplication is an algebra map.
- `transcendental_of_isPrimitiveElem`: in a domain bialgebra, a nonzero
  primitive element is transcendental. It has counit zero, so the Library
  `transcendental_of_augmentation_eq_zero` applies.
- `exists_common_of_primitive`: let `k` be perfect and `B` a domain. If
  primitive `y, t` satisfy `α(y) = β(t)` with nonzero additive `α, β`, then
  `y = A(s)` and `t = A'(s)` for a primitive `s` and additive `A, A'`. This is
  `exists_common_of_relation` (from `Additive`), applied to the set of
  primitive elements. That set is closed under subtraction and additive
  polynomials, and a primitive root of a nonzero polynomial is zero by
  transcendence.
- `finrank_quotient_span_lt`: in a domain, if `s ≠ 0`, `b` is not a unit and
  `B/(s b)` is finite-dimensional, then `dim B/(s) < dim B/(s b)`. The
  surjection `B/(s b) → B/(s)` has nonzero kernel, which contains the class
  of `s`.

## Main result

`exists_primitive_bijective` works in the Library bialgebra `bialgebra e` on
the coordinate algebra `B` of a corepresented group over a perfect field `k`.
Assume:

- `B` and `B ⊗ B` are domains;
- `OneMemStable k B` holds;
- some `a ∈ B` is not a constant (`hconst`);
- for every nonzero primitive `z`, the quotient `B/(z)` is finite-dimensional
  (`hfin`);
- any two primitive elements satisfy a nonzero polynomial relation
  `c(y, t) = 0` with `c : k[X][X]` (`hdep`);
- for every nonzero primitive `z` and nonconstant `g`, `g(z)` is not a unit
  (`hunit`).

Then there is a primitive `y` for which `aeval y : k[X] → B` is bijective.

## Implemented argument

The Library `exists_nonzero_primitive_of_oneMemStable` supplies nonzero
primitive elements. Choose one, `y`, minimizing `dim_k B/(y)` (`Nat.find`).
`aeval y` is injective because `y` is transcendental.

For surjectivity, suppose `b ∉ k[y]`. `exists_primitive_not_mem_polys` gives a
primitive `t ∉ k[y]`. By `hdep` and `exists_additive_relation`, there are
additive `α, β`, not both zero, with `α(y) + β(t) = 0`. Both are nonzero,
because `y` and `t` are nonzero and transcendental.
`exists_common_of_primitive` then gives a primitive `s` with `y = A(s)` and
`t = A'(s)`, where `s ≠ 0` and `A` has no constant term.

- If `deg A ≤ 1`, then `A = a X` with `a ≠ 0`. So `s = a⁻¹ y` and
  `t = A'(a⁻¹ y) ∈ k[y]`, a contradiction.
- Otherwise `A = X · A₁` with `deg A₁ > 0`, so `y = s · A₁(s)`. By `hunit`,
  `A₁(s)` is not a unit, and `finrank_quotient_span_lt` gives
  `dim B/(s) < dim B/(y)`. This contradicts the minimality of `y`.
