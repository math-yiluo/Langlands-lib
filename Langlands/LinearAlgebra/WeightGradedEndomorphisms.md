# Endomorphisms of a weight-graded vector space

Module `Langlands.LinearAlgebra.WeightGradedEndomorphisms`, namespace
`Langlands.LinearAlgebra.WeightGraded`.

Throughout, `k` is a field, `U` a `k`-vector space, `X` an additive commutative
group, and `W : X → Submodule k U` a family of subspaces ("weight spaces"). The
module collects elementary linear algebra about endomorphisms of `U` that are
homogeneous for the grading by `X`. It is used in the Casimir proof of
Freudenthal's multiplicity formula, where `U` is the product of the coordinate
spaces of two representations and `W μ` is its torus weight-`μ` space. Nothing
here is taken from the literature; these are standard facts about graded
endomorphisms, proved directly.

## Homogeneous endomorphisms

- `shift W χ`: the subspace of endomorphisms `f` with `f (W μ) ⊆ W (μ + χ)` for
  every `μ` ("degree `χ`"). `mem_shift` unfolds membership.
- `mapsTo_of_mem_shift`: a degree-`χ` endomorphism maps `W μ` into `W ν`
  whenever `μ + χ = ν`.
- `mul_mem_shift`, `commutator_mem_shift`: the product and the commutator
  `f g - g f` of endomorphisms of degrees `χ` and `χ'` have degree `χ + χ'`.

## Endomorphisms acting by scalars on the weight spaces

- `IsScalarOn W φ t`: for every `μ`, `t` acts on `W μ` as multiplication by the
  scalar `φ μ`.
- `IsScalarOn.mem_shift_zero`: such a `t` has degree `0`.
- `IsScalarOn.add`, `IsScalarOn.smul`, `IsScalarOn.mul`, `isScalarOn_zero`,
  `IsScalarOn.sum`: the property is preserved by sums, scalar multiples,
  products and finite sums, with the scalar functions combined the same way.
- `ext_of_iSup_eq_top`: if the `W μ` span `U`, two endomorphisms that agree on
  every `W μ` are equal. The proof is induction over the supremum
  (`Submodule.iSup_induction'`).
- `IsScalarOn.commutator`: if the `W μ` span `U`, `t` acts on `W μ` by `φ μ`
  and `φ` is additive, then `t f - f t = φ χ • f` for every `f` of degree `χ`.
  Both sides agree on each `W μ`, because `t f u = φ(μ + χ) f u` and
  `f t u = φ μ f u`.

## Finite-dimensional facts

Assume now that `U` is finite-dimensional, the family `W` is independent
(`iSupIndep W`) and, where stated, spans `U` (`⨆ μ, W μ = ⊤`).

- `finite_ne_bot`: only finitely many `W μ` are nonzero (Mathlib's
  `Submodule.finite_ne_bot_of_iSupIndep`).
- `isInternal`: `U` is the internal direct sum of the `W μ`. This needs only
  independence and spanning, not finite-dimensionality.
- `trace_eq_zero_of_mem_shift`: an endomorphism of nonzero degree `χ` has trace
  zero. It maps each `W μ` into a different summand `W (μ + χ)`, and Mathlib's
  `LinearMap.trace_eq_zero_of_mapsTo_ne` applies.
- `trace_eq_finsum_of_isScalarOn`: if `t` acts on `W μ` by `φ μ`, then
  `trace t = ∑ᶠ μ, dim (W μ) · φ μ`. The proof uses Mathlib's
  `LinearMap.trace_eq_sum_trace_restrict'` and computes each restriction as
  `φ μ • id`.

When moreover `X` is torsion-free (`IsAddTorsionFree X`):

- `exists_forall_ge_eq_bot`: for `α ≠ 0` and any `μ`, there is `N` with
  `W (μ + j • α) = ⊥` for all `j ≥ N`. The map `j ↦ μ + j • α` is injective
  because `X` is torsion-free. So only finitely many `j` have a nonzero weight
  space.
- `isNilpotent_of_mem_shift`: an endomorphism of nonzero degree is nilpotent.
  On `W μ`, its `j`-th power lands in `W (μ + j • χ)`, which is zero for large
  `j`. Then Mathlib's `Module.End.isNilpotent_iff_of_finite` and induction over
  the supremum give nilpotency.
