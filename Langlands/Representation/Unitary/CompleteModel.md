# Complete models of form-dependent Hilbert completions

This internal construction takes a group `G`, an algebraic complex
representation `ρ` on `V`, and an invariant positive definite form `b`.
The universes of `G`, `V` and the model `E` are independent. The model is a
genuine complex inner-product space with its norm topology. The supplied
complex-linear equivalence `e : V ≃ₗ[ℂ] E` must satisfy the exact identity
`inner ℂ (e v) (e w) = b.inner v w`. No topology is imposed on `V`.

`normedModelEquiv` transports `e` through the published identification with
`b.NormedCarrier`, and uses `LinearEquiv.isometryOfInner`. Its value on the
identified original vector is `e v`. Isometry and the norm of the completion
embedding give `model_norm_eq_toHilbert`.

When `E` is complete, `completeModelEquiv` applies Mathlib's
`LinearEquiv.extendOfIsometry` to `e`, the actual canonical embedding
`b.toHilbert` and the identity map of `E`. The former has dense range by the
published completion theorem; the latter is surjective. The preceding norm
identity is the remaining input. The result is an actual complex-linear
isometric equivalence

```text
b.HilbertCompletion ≃ₗᵢ[ℂ] E.
```

The two embedded-vector formulas are

```text
completeModelEquiv (b.toHilbert v) = e v,
completeModelEquiv.symm y = b.toHilbert (e.symm y).
```

They are the corresponding Mathlib extension formulas. Norm and inner-product
preservation in both directions, continuity and bijectivity are part of the
linear isometric equivalence structure. `toHilbert_surjective_of_completeModel`
uses injectivity and the first formula to show that every completed vector is
already an original vector under the canonical embedding. This conclusion
requires the supplied complete model and is not asserted for a general form.

`completeModelEquiv_unique` proves uniqueness among continuous complex-linear
maps having the first formula. The equality set is closed, and it contains
the dense embedded carrier.

`completeModelEquiv_covariant` takes an original complex-linear operator `a`,
a continuous linear operator `A` on the completion satisfying
`A (b.toHilbert v) = b.toHilbert (a v)`, and a continuous linear operator `D`
on `E` satisfying `e (a v) = D (e v)`. The same closed-equality and density
argument proves `completeModelEquiv (A x) = D (completeModelEquiv x)` for
every completed vector. `completeModelEquiv_completedOperator` specializes
this to the published completed group operators. This needs no topology
on the group and makes no claim of joint action continuity.

The provenance is internal: the construction composes the published
form-dependent completion with the pinned Mathlib inner-product isometry
and dense isometric extension constructions. The uniqueness, surjectivity
and covariance proofs above are intrinsic consequences. No new
original-literature identification is asserted. Existence of a complete
form-preserving model for an arbitrary representation remains a separate
obligation, and unbounded operators receive no extension here.
