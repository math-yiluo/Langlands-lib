# Invariants of exact sequences of complex representations

`Langlands.Weil.representationExactSequenceInvariants` proves the existing
`Langlands.Weil.RepresentationExactSequenceInvariants` from
`Langlands.Weil.Representation.Operations`, with the group universe and all
three carrier universes independent. The imported statement and its paired
Markdown are unchanged.

For actual intertwiners `f : ρ.IntertwiningMap σ` and
`g : σ.IntertwiningMap τ`, the hypotheses are injectivity of `f`,
surjectivity of `g`, and `range f.toLinearMap = ker g.toLinearMap`.
The conclusions are

```
finrank ℂ U = finrank ℂ V + finrank ℂ T
det (σ w) = det (ρ w) * det (τ w)    for every w : G.
```

There is no positive-dimension assumption: the proof applies to zero
carriers and uses Mathlib's usual determinant, equal to one in dimension
zero. No topology, finite group or image, semisimplicity, representation
splitting, invariant complement, or input basis is required.

## Implemented proof

The reusable theorem `exactSequence_finrank` sets up the linear equivalences
`V ≃ₗ[ℂ] ker g.toLinearMap` and
`(U ⧸ ker g.toLinearMap) ≃ₗ[ℂ] T`. The first is
`LinearEquiv.ofInjective f.toLinearMap hf` followed by
`LinearEquiv.ofEq` for the exactness equality; the second is
`LinearMap.quotKerEquivOfSurjective` applied to `g`. Their `finrank_eq`
identities turn `Submodule.finrank_quotient_add_finrank` into the desired
formula, after commuting the two summands.

The reusable theorem `exactSequence_det` takes `W = ker g.toLinearMap`.
Intertwining of `g` implies `W ≤ W.comap (σ w)`: a vector killed by `g`
is still killed after applying `σ w`. Thus there are actual endomorphisms
`(σ w).restrict hW` of `W` and `W.mapQ W (σ w) hW` of `U ⧸ W`.

The same equivalence from `V` to `W` conjugates `ρ w` to the restricted
operator. This is checked after coercion to `U`, using the intertwining
equation for `f` and the inverse law for the equivalence. The quotient
equivalence conjugates the induced quotient operator to `τ w`. To check
this equality at `t : T`, surjectivity writes `t = g u`; the inverse
quotient equivalence sends this to the class of `u`, and the equality
reduces to the intertwining equation for `g`.

`LinearMap.det_conj` identifies the determinants in these two comparisons.
Finally, `LinearMap.det_eq_det_mul_det W (σ w) hW` factors the determinant
of `σ w` into those of its restriction and quotient, giving the result.
Mathlib proves this factorization using a basis of the submodule and
quotient and a block triangular matrix. All such choices are internal;
there is no assertion of a splitting as representations.

The two helpers require finite dimension only of the middle carrier `U`;
the equivalences suffice for their uses of finrank and determinant.
The closing theorem retains exactly the original target, including its
finite-dimensional hypotheses on all three carriers, and joins the two
helper conclusions.

## Provenance and scope

This is an internal finite-dimensional linear-algebra derivation of the
published target. Worker 48 implemented the proof; Worker 4 supplied the
kernel/quotient determinant route in the task context and pointed to the
published determinant-conjugacy calculation. The implementation imports
existing definitions and proves no other clause of `RepresentationOperations`.

The target's source boundary is Tate, *Number theoretic background*,
Corvallis Part II (1979), section 2 opening, printed page 9/PDF page 18,
literature ID `tate-1979-number-theoretic-background`, retained `Part II.pdf`
SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
That original passage defines exact-sequence additivity for functions on
representations to descend to virtual representations and discusses
dimension and determinant. It is motivation for the target, not a quoted
proof of these two formulas. Worker 48 read this passage. The proof above
is algebraic and needs none of the topological assumptions used in Tate's
surrounding discussion.

The Mathlib inputs are from the pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0:
`LinearAlgebra/Determinant.lean` (`det_conj`, `det_eq_det_mul_det`),
`LinearAlgebra/Dimension/RankNullity.lean`,
`LinearAlgebra/Isomorphisms.lean`,
`Algebra/Module/Submodule/Equiv.lean`, and
`RepresentationTheory/Intertwining.lean`.

## Verification

The proof and a private check module compiled without warnings in the pinned
environment. The check assigns the unapplied closing constant both to the
published proposition and to its complete expanded telescope, with four
independent universe levels. Declaration inspection reports precisely
`uG`, `uV`, `uU`, `uT` and only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. Formal exact-target validation and
independent semantic review are separate submission requirements.
